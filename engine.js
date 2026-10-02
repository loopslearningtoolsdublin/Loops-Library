/**
 * LOOPS ENGINE — shared game engine for all Loops Learning Tools games.
 * One file, used by every published game (linked, not copy-pasted), so a fix
 * here fixes every game in the library at once.
 *
 * Usage in a published game file:
 *   <div id="loopsApp"></div>
 *   <script src="../engine.js"></script>
 *   <script>
 *     const GAME_DATA = { slug, name, emoji, category, background, loops: [...] };
 *     (optional) lang: { q: "en", a: "es" } — question / answer language, used
 *     for read-aloud voices and voice answers. Missing = English throughout.
 *     LoopsEngine.init(GAME_DATA);
 *   </script>
 *
 * GAME_DATA shape:
 *   {
 *     slug: "world-capitals",
 *     name: "World Capitals",
 *     emoji: "🌍",
 *     category: "Language",
 *     background: null,            // optional base64/url
 *     loops: [
 *       { name: "Loop 1", emoji: "🟦", timeLimit: 15, qs: [
 *           { type:"mc", q:"...", a:"Paris", opts:["Paris","Berlin","Rome","Madrid"] },
 *           { type:"typed", q:"...", a:"paris" }
 *       ]}
 *     ]
 *   }
 *
 * MASTERY / WEAK SPOTS
 * Every question is answered correctly at least MASTERY_TARGET (10) times
 * before it's considered learned. The first time a question is missed —
 * anywhere, in any loop — it starts being tracked in save.mastery as a
 * running correct-count. It never resets on a further miss, it just sits at
 * whatever count it's at until it reaches 10. Any tracked-but-not-mastered
 * question is a "weak spot" and stays pullable into review regardless of
 * which loop it originally came from — mistakes follow you across the whole
 * game, not just within the loop you made them in.
 */
(function () {
  "use strict";

  var MASTERY_TARGET = 10;
  var ICON_SPEAKER = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M11 5 6 9H3v6h3l5 4V5z"/><path d="M15.5 8.5a5 5 0 0 1 0 7"/><path d="M18.5 5.5a9 9 0 0 1 0 13"/></svg>';
  var ICON_MIC = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="9" y="3" width="6" height="11" rx="3"/><path d="M5 11a7 7 0 0 0 14 0"/><path d="M12 18v3"/></svg>';

  var GAME = null;
  var save = null;
  var QUESTION_INDEX = []; // flat list of { key, q, loopIdx } across all loops
  var G = { mode: "loop", loopIdx: 0, queue: [], qi: 0, correct: 0, wrongs: 0, requeued: null, seenKeys: null, firstTryCorrect: 0, answered: false, timer: null, t: 0, startMs: 0, lastUserAnswer: null, roundLog: null };

  // ── STORAGE ──
  function saveKey() { return "loops_save_" + GAME.slug; }
  function loadSave() {
    try { save = JSON.parse(localStorage.getItem(saveKey())) || {}; }
    catch (e) { save = {}; }
    if (typeof save.unlocked !== "number") save.unlocked = 0;
    if (!save.best) save.best = {};
    if (!save.bestScore) save.bestScore = {};
    if (!save.mastery) save.mastery = {}; // { questionKey: correctCount }
    if (!save.plays) save.plays = {};     // { loopIdx: times completed } — the card's Grit stat
    if (!save.bestStreak) save.bestStreak = {}; // { loopIdx: longest run right in a row } — for the saved card
    if (!save.ws) save.ws = { rounds: 0, bestGain: 0, bestTime: 0, bestStreak: 0 }; // Weak Spots card: rounds played + personal bests
  }
  function persist() { try { localStorage.setItem(saveKey(), JSON.stringify(save)); } catch (e) {} }

  // ── HELPERS ──
  function el(id) { return document.getElementById(id); }
  function shuffle(arr) {
    var a = arr.slice();
    for (var i = a.length - 1; i > 0; i--) {
      var j = Math.floor(Math.random() * (i + 1));
      var tmp = a[i]; a[i] = a[j]; a[j] = tmp;
    }
    return a;
  }
  function normalise(s) {
    return (s || "").toString().trim().toLowerCase().replace(/[^\w\sáéíóúüñàèìòùâêîôûäëïöüçãõ]/gi, "");
  }
  function fmtTime(sec) { return sec ? sec.toFixed(1) + "s" : "—"; }
  function questionKey(q) { return normalise(q.q) + "|" + normalise(q.a); }

  // ── SOFT MATCHING for typed answers ──
  // Exact-string matching alone punishes real typos and minor valid phrasing
  // even when the underlying answer is correct. This allows small, scaled
  // edit-distance leniency instead — a genuine typo still counts, wildly
  // different answers still don't.
  function levenshtein(a, b) {
    var m = a.length, n = b.length;
    if (m === 0) return n;
    if (n === 0) return m;
    var d = [];
    for (var i = 0; i <= m; i++) { d[i] = [i]; }
    for (var j = 0; j <= n; j++) { d[0][j] = j; }
    for (var i2 = 1; i2 <= m; i2++) {
      for (var j2 = 1; j2 <= n; j2++) {
        var cost = a[i2 - 1] === b[j2 - 1] ? 0 : 1;
        d[i2][j2] = Math.min(
          d[i2 - 1][j2] + 1,
          d[i2][j2 - 1] + 1,
          d[i2 - 1][j2 - 1] + cost
        );
        // Treat adjacent transpositions (e.g. "ei" vs "ie") as a single edit,
        // since that's one of the most common real typing mistakes.
        if (i2 > 1 && j2 > 1 && a[i2 - 1] === b[j2 - 2] && a[i2 - 2] === b[j2 - 1]) {
          d[i2][j2] = Math.min(d[i2][j2], d[i2 - 2][j2 - 2] + 1);
        }
      }
    }
    return d[m][n];
  }

  function matchTyped(userInput, correctAnswer) {
    var a = normalise(userInput);
    var b = normalise(correctAnswer);
    if (a === b) return { correct: true, exact: true };
    if (a.length === 0) return { correct: false, exact: false };
    // Short answers get no leniency — too easy for a genuinely different
    // short word to slip through (e.g. "cat" vs "car").
    var threshold = b.length <= 3 ? 0 : Math.min(3, Math.max(1, Math.floor(b.length / 6)));
    var dist = levenshtein(a, b);
    return { correct: dist <= threshold, exact: false, distance: dist };
  }

  function diffHighlight(userInput, correctAnswer) {
    var a = (userInput || "").toString();
    var b = (correctAnswer || "").toString();
    var out = "";
    var len = Math.max(a.length, b.length);
    for (var i = 0; i < len; i++) {
      var ca = a[i], cb = b[i];
      if (ca !== undefined && ca.toLowerCase() === (cb || "").toLowerCase()) {
        out += ca;
      } else if (cb !== undefined) {
        out += '<span style="background:#fef08a;border-radius:3px;padding:0 1px;">' + cb + '</span>';
      }
    }
    return out;
  }

  var CORRECT_PHRASES = ["✔ Nice one!", "✔ Got it!", "✔ Sharp!", "✔ Yes!", "✔ Correct!", "✔ Nailed it!"];
  var WRONG_PHRASES = ["Not quite", "So close", "Almost", "Not this time"];
  function pick(arr) { return arr[Math.floor(Math.random() * arr.length)]; }

  // ── DUBLIN ENCOURAGEMENT ── a few in-play toasts (max 2 a round, never in
  // the first 3 questions, never on back-to-back questions) and a line that
  // always tops the finish screen, picked by how the round went.
  var CHEER_PLAY = ["Ah here, you're flyin'!", "Stop the lights!", "Deadly.", "Keep her lit.", "Only savage, so it is.",
    "Go on, ya good thing!", "Fair play to ya.", "Lethal.", "You're on fire, so ya are.", "Massive.", "Now we're motoring.",
    "Look at you go.", "Sharp as a tack.", "Nailing it.", "Class act.", "Not a bother on ya.", "Steady hands.", "That's the stuff.",
    "Grand job. Well, better than grand.", "Brain's warmed up now.", "Mighty.", "You're well able.", "Cool as you like."];
  var CHEER_COMEBACK = ["Back on track. Lovely.", "Shook it off. Good stuff."];
  var CHEER_END = {
    perfect: ["Ten outta ten. Stop the lights!", "Not one dropped.", "Flawless. Take a bow."],
    pb: ["There you are!", "There you are. New best.", "Beat yourself. Best kind of win."],
    strong: ["Sound out. Nearly perfect.", "Cracking round.", "That's a proper score."],
    middle: ["Getting there. It's sticking.", "Solid. Next one's better.", "Halfway up the hill. Keep climbing."],
    tough: ["Hard one, fair play for finishing.", "Every go makes it stick.", "Tough loop. You'll get it next time."],
    all: ["The whole lot, done. Absolute legend.", "Five loops. Job done.", "Finished the lot. Take that."],
    review: ["Weak spots getting stronger. Deadly.", "Fixed what was broken. Class."]
  };
  var cheerBag = [], cheerTimer = null;
  var STAMP_SVG = '<svg class="stampsvg" viewBox="0 0 120 120" aria-hidden="true"><defs><filter id="rough"><feTurbulence type="fractalNoise" baseFrequency=".9" numOctaves="2" seed="3"/><feDisplacementMap in="SourceGraphic" scale="2.2"/></filter><path id="ring" d="M60,60 m-44,0 a44,44 0 1,1 88,0 a44,44 0 1,1 -88,0"/></defs><g filter="url(#rough)" fill="none" stroke="#1B2A8C"><circle cx="60" cy="60" r="56" stroke-width="4"/><circle cx="60" cy="60" r="36" stroke-width="2"/><text font-family="Arial Black,Arial,sans-serif" font-weight="900" font-size="13" letter-spacing="2" fill="#1B2A8C" stroke="none"><textPath href="#ring" startOffset="0" textLength="270" lengthAdjust="spacing">LOOPS ★ DUBLIN ★ APPROVED ★</textPath></text><image href="data:image/png;base64,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" x="33" y="33" width="54" height="54"/></g></svg>';
  function stampHtml() { return '<span class="loops-stamp">' + STAMP_SVG + '</span>'; }
  function nextCheer(list) {
    // shuffle-bag: every line comes round before any repeats
    if (list !== CHEER_PLAY) return pick(list);
    if (!cheerBag.length) cheerBag = shuffle(CHEER_PLAY.slice());
    return cheerBag.pop();
  }
  function showToast(text) {
    var t = el("loopsToast"); if (!t) return;
    t.textContent = text;
    t.insertAdjacentHTML("beforeend", stampHtml());
    t.classList.remove("on"); void t.offsetWidth; t.classList.add("on");
    clearTimeout(cheerTimer);
    cheerTimer = setTimeout(function () { t.classList.remove("on"); }, 1400);
  }
  function hideToast() { var t = el("loopsToast"); if (t) t.classList.remove("on"); clearTimeout(cheerTimer); }
  function maybeCheer(ok) {
    var prevMiss = G.lastWasMiss; G.lastWasMiss = !ok;
    if (ok) G.run = (G.run || 0) + 1; else G.run = 0;
    if (!ok || G.qi < 3 || (G.cheers || 0) >= 2 || G.lastCheerQi === G.qi - 1) return;
    var comeback = prevMiss, streak = G.run >= 3;
    var chance = comeback || streak ? 0.35 : 0.15;
    if (Math.random() >= chance) return;
    G.cheers = (G.cheers || 0) + 1; G.lastCheerQi = G.qi;
    showToast(comeback ? pick(CHEER_COMEBACK) : nextCheer(CHEER_PLAY));
  }
  function setCheerBanner(kind) {
    var b = el("loopsCheer"); if (!b) return;
    var line = nextCheer(CHEER_END[kind]);
    b.textContent = line;
    b.insertAdjacentHTML("beforeend", stampHtml());
    b.style.display = "block";
    setTimeout(function () { showToast(line); }, 250); // always pops at the end, then stays as the banner
  }

  function buildQuestionIndex() {
    QUESTION_INDEX = [];
    GAME.loops.forEach(function (loop, loopIdx) {
      loop.qs.forEach(function (q) {
        QUESTION_INDEX.push({ key: questionKey(q), q: q, loopIdx: loopIdx });
      });
    });
  }

  function weakSpots() {
    var seen = {};
    var out = [];
    QUESTION_INDEX.forEach(function (item) {
      var count = save.mastery[item.key];
      if (count !== undefined && count < MASTERY_TARGET && !seen[item.key]) {
        seen[item.key] = true;
        out.push(item);
      }
    });
    return out;
  }

  // Weak Spots as a pile of steps: every tracked question is worth
  // MASTERY_TARGET steps, every right answer takes one off. "left" shrinks
  // as they work; "total" only grows when a new question is missed.
  function wsPile() {
    var total = 0, left = 0, seen = {};
    QUESTION_INDEX.forEach(function (item) {
      var c = save.mastery[item.key];
      if (c === undefined || seen[item.key]) return;
      seen[item.key] = true;
      total += MASTERY_TARGET;
      left += Math.max(0, MASTERY_TARGET - c);
    });
    return { total: total, left: left, done: total - left };
  }
  function wsBarHtml(p, gain) {
    var donePct = p.total ? Math.round(100 * (p.done - (gain || 0)) / p.total) : 0;
    var gainPct = p.total ? Math.round(100 * (gain || 0) / p.total) : 0;
    return '<div class="loops-ws-bar"><span class="old" style="width:' + donePct + '%"></span><span class="new" style="width:' + gainPct + '%"></span></div>';
  }

  // ── SOUND ──
  var _ctx = null;
  function beep(freq, dur, type, vol) {
    try {
      var Ctx = window.AudioContext || window.webkitAudioContext;
      if (!_ctx) _ctx = new Ctx();
      if (_ctx.state === "suspended") _ctx.resume();
      var now = _ctx.currentTime;
      var osc = _ctx.createOscillator();
      var gain = _ctx.createGain();
      osc.type = type || "triangle";
      osc.frequency.setValueAtTime(freq, now);
      gain.gain.setValueAtTime(0.0001, now);
      gain.gain.exponentialRampToValueAtTime(vol || 0.03, now + 0.01);
      gain.gain.exponentialRampToValueAtTime(0.0001, now + (dur || 0.12));
      osc.connect(gain); gain.connect(_ctx.destination);
      osc.start(now); osc.stop(now + (dur || 0.12) + 0.02);
    } catch (e) {}
  }
  function toneGood() { beep(660, 0.08, "triangle", 0.03); setTimeout(function () { beep(880, 0.1, "triangle", 0.03); }, 80); }
  function toneBad() { beep(220, 0.12, "sawtooth", 0.025); }
  function toneStart() { beep(392, 0.1, "triangle", 0.025); setTimeout(function () { beep(523, 0.12, "triangle", 0.03); }, 80); }
  function toneWin() { beep(523, 0.08, "triangle", 0.03); setTimeout(function () { beep(659, 0.08, "triangle", 0.03); }, 80); setTimeout(function () { beep(784, 0.12, "triangle", 0.035); }, 160); }
  function toneMastered() { beep(784, 0.09, "triangle", 0.035); setTimeout(function () { beep(988, 0.09, "triangle", 0.035); }, 90); setTimeout(function () { beep(1175, 0.14, "triangle", 0.04); }, 180); }

  function confetti() {
    for (var i = 0; i < 24; i++) {
      (function (i) {
        var p = document.createElement("div");
        p.style.cssText = "position:fixed;left:" + (Math.random() * 100) + "vw;top:-20px;width:10px;height:14px;border-radius:3px;" +
          "background:" + (i % 2 === 0 ? "#ffd43b" : "#00c2b3") + ";z-index:9999;pointer-events:none;opacity:.95;" +
          "transform:rotate(" + (Math.random() * 360) + "deg);transition:transform 1.5s ease-out, top 1.5s ease-out, opacity 1.5s ease-out;";
        document.body.appendChild(p);
        requestAnimationFrame(function () {
          p.style.top = "105vh";
          p.style.transform = "translateX(" + ((Math.random() - 0.5) * 160) + "px) rotate(" + (Math.random() * 720) + "deg)";
          p.style.opacity = "0.08";
        });
        setTimeout(function () { p.remove(); }, 1600);
      })(i);
    }
  }

  // ── STYLES ──
  // ── CATEGORY COLOURS ──
  // Fallback palette only, for games published before the taxonomy went
  // dynamic. Any game published after that point carries its own resolved
  // {pastel,deep,wash} triplet baked into GAME.colors at publish time (see
  // categoryColors() below) — this hardcoded map never needs to learn about
  // a new/promoted category, since new games just bring their colour with
  // them. "Misc" is kept as an alias of "Other" so games published under
  // the old category name before the rename still render correctly without
  // needing to be republished.
  var CATEGORY_COLORS = {
    "Language": { pastel: "#C1F0EA", deep: "#2FB18A", wash: "#EBF6F0" },
    "Onboarding": { pastel: "#FBE4B7", deep: "#D9A03F", wash: "#FBF3E2" },
    "Compliance": { pastel: "#D0E0F6", deep: "#4F7FC7", wash: "#EFF1F3" },
    "Exam Prep": { pastel: "#E2D8FA", deep: "#8B67D9", wash: "#F4EFF4" },
    "Other": { pastel: "#FAD2C3", deep: "#E0784E", wash: "#FAEEE5" },
    "Misc": { pastel: "#FAD2C3", deep: "#E0784E", wash: "#FAEEE5" }
  };
  var AMBER = "#F8CE7C"; // Weak Spots accent — deliberately category-independent so it reads the same everywhere

  function categoryColors() {
    if (GAME && GAME.colors && GAME.colors.pastel) return GAME.colors;
    return CATEGORY_COLORS[(GAME && GAME.category)] || CATEGORY_COLORS["Language"];
  }

  // Navy or white text, whichever reads better on a given category colour.
  function inkOn(hex) {
    var h = String(hex || "").replace("#", "");
    if (h.length !== 6) return "#0D2A52";
    var c = [0, 2, 4].map(function (i) {
      var v = parseInt(h.slice(i, i + 2), 16) / 255;
      return v <= 0.03928 ? v / 12.92 : Math.pow((v + 0.055) / 1.055, 2.4);
    });
    return (0.2126 * c[0] + 0.7152 * c[1] + 0.0722 * c[2]) > 0.28 ? "#0D2A52" : "#ffffff";
  }

  // A game's colours are fixed when it's added, but its category can change
  // later (a shelf gets promoted). Ask the library for this game's current
  // category so the game always matches its tile. Fails quietly — the baked
  // colours stay if the library can't be reached.
  function syncCategoryFromLibrary() {
    if (!window.fetch || !GAME || !GAME.slug) return;
    fetch("../games.json", { cache: "no-cache" })
      .then(function (r) { return r.ok ? r.json() : null; })
      .then(function (data) {
        if (!data || !data.games || !data.categories) return;
        var entry = null;
        for (var i = 0; i < data.games.length; i++) if (data.games[i].slug === GAME.slug) { entry = data.games[i]; break; }
        // Older games got their tile picture after they were made — use it on the card too.
        if (entry && entry.thumbnail && !GAME.background) GAME.background = "../" + entry.thumbnail;
        var c = entry && data.categories[entry.category];
        if (!c || !c.deep || !c.pastel || !c.wash) return;
        if (GAME.colors && GAME.colors.deep === c.deep && GAME.category === entry.category) return;
        GAME.category = entry.category;
        GAME.colors = { pastel: c.pastel, deep: c.deep, wash: c.wash };
        var old = document.getElementById("loopsEngineStyles");
        if (old) old.parentNode.removeChild(old);
        injectStyles();
      })
      .catch(function () {});
  }

  function injectStyles() {
    if (document.getElementById("loopsEngineStyles")) return;
    var cat = categoryColors();
    var ink = inkOn(cat.deep);
    var css = "" +
      // Uniform with the library: the page takes the category's soft tint,
      // and the bold (deep) shade marks the title band, level tiles and timer.
      "body{background:linear-gradient(160deg," + cat.pastel + " 0%," + cat.wash + " 55%,#F7F5F0 100%) fixed !important;}" +
      "#loopsApp{--navy:#0D2A52;--cat:" + cat.pastel + ";--catDeep:" + cat.deep + ";--catInk:" + ink + ";--catWash:" + cat.wash + ";--amber:" + AMBER + ";--ink:#0D2A52;--red:#c94c4c;" +
      "font-family:'Inter',system-ui,-apple-system,Segoe UI,Roboto,sans-serif;color:var(--ink);max-width:520px;margin:0 auto;padding:16px;" +
      "background:var(--catWash);border-radius:20px;}" +
      ".loops-screen{display:none;} .loops-screen.active{display:block;}" +
      ".loops-header{text-align:center;margin-bottom:18px;background:var(--catDeep);color:var(--catInk);border-radius:16px;padding:14px 12px 12px;box-shadow:0 6px 16px rgba(13,42,82,.15);} .loops-header h1{font-family:'Playfair Display',serif;font-size:1.5rem;margin:6px 0 2px;}" +
      ".loops-header .sub{opacity:.8;font-size:.9rem;}" +
      ".loops-header .loops-logo-mark{height:36px;width:auto;border-radius:5px;margin-bottom:4px;}" +
      ".loops-grid{display:grid;gap:12px;}" +
      ".loops-tile{background:#fff;border:2px solid transparent;border-left:6px solid var(--catDeep);border-radius:14px;padding:16px;cursor:pointer;transition:.15s;box-shadow:0 4px 14px rgba(13,42,82,.1);}" +
      ".loops-tile.locked{opacity:.55;cursor:not-allowed;}" +
      ".loops-tile:not(.locked):hover{border-color:var(--catDeep);transform:translateY(-2px);}" +
      ".loops-tile.weak{border-color:var(--amber);border-left-color:var(--amber);background:#fffbea;}" +
      ".loops-tile.halfway{border-color:var(--catDeep);background:#fff;}" +
      ".loops-tile-top{display:flex;align-items:center;gap:10px;font-weight:800;font-size:1.05rem;}" +
      ".loops-tile-meta{font-size:.82rem;opacity:.7;margin-top:6px;}" +
      ".loops-badge{display:inline-block;background:var(--amber);color:#5c4415;font-size:.72rem;font-weight:800;padding:2px 8px;border-radius:10px;margin-left:6px;}" +
      ".loops-timerwrap{width:100%;height:6px;background:rgba(13,42,82,.15);border-radius:3px;overflow:hidden;margin-bottom:14px;}" +
      "#loopsTimerBar{height:100%;background:var(--catDeep);transition:width .1s linear,background .3s;}" +
      ".loops-q{font-size:1.2rem;font-weight:800;margin-bottom:18px;line-height:1.4;}" +
      ".loops-opts{display:flex;flex-direction:column;gap:10px;}" +
      ".loops-opt{padding:13px;border:2px solid transparent;border-radius:10px;background:#fff;text-align:left;font-weight:600;cursor:pointer;font-size:1rem;box-shadow:0 3px 10px rgba(13,42,82,.08);}" +
      ".loops-opt:hover:not(:disabled){border-color:var(--catDeep);}" +
      ".loops-opt.correct{background:#dcfce7;border-color:#86efac;color:#166534;}" +
      ".loops-opt.wrong{background:#fee2e2;border-color:#fca5a5;color:#991b1b;}" +
      ".loops-opt.faded{opacity:.45;}" +
      ".loops-input{width:100%;padding:13px;border:2px solid transparent;border-radius:10px;font-size:1rem;margin-bottom:10px;box-shadow:0 3px 10px rgba(13,42,82,.08);}" +
      ".loops-btn{padding:12px 20px;border-radius:100px;border:none;font-size:1rem;cursor:pointer;color:#fff;font-weight:700;" +
      "background:linear-gradient(135deg,var(--navy),#163f78);width:100%;}" +
      ".loops-btn.ghost{background:transparent;color:var(--navy);border:2px solid rgba(13,42,82,.25);}" +
      ".loops-btn:disabled{opacity:.5;cursor:not-allowed;}" +
      ".loops-meta-row{display:flex;justify-content:space-between;align-items:center;margin-bottom:10px;font-size:.85rem;}" +
      ".loops-q,.loops-fb,.loops-breakdown{-webkit-user-select:none;user-select:none;-webkit-touch-callout:none;}" +
      ".loops-q-row{display:flex;gap:10px;align-items:flex-start;margin-bottom:18px;} .loops-q-row .loops-q{margin-bottom:0;flex:1;}" +
      ".loops-icon-btn{flex-shrink:0;width:36px;height:36px;border-radius:100px;border:1.5px solid rgba(13,42,82,.18);background:#fff;color:var(--navy);display:inline-flex;align-items:center;justify-content:center;cursor:pointer;padding:0;box-shadow:0 2px 6px rgba(13,42,82,.06);transition:background .2s,color .2s,border-color .2s;}" +
      ".loops-icon-btn svg{width:17px;height:17px;} .loops-icon-btn.active{background:var(--navy);color:#fff;border-color:var(--navy);}" +
      ".loops-icon-btn.listening{background:var(--red);border-color:var(--red);color:#fff;animation:loopsPulse 1.2s infinite;}" +
      "@keyframes loopsPulse{0%{box-shadow:0 0 0 0 rgba(201,76,76,.45);}70%{box-shadow:0 0 0 10px rgba(201,76,76,0);}100%{box-shadow:0 0 0 0 rgba(201,76,76,0);}}" +
      ".loops-input-wrap{position:relative;} .loops-input-wrap .loops-input{padding-right:54px;} .loops-input-wrap .loops-icon-btn{position:absolute;right:7px;top:7px;}" +
      ".loops-moretime{display:flex;align-items:center;justify-content:center;gap:10px;margin-top:18px;font-size:.85rem;font-weight:700;color:var(--navy);opacity:.8;cursor:pointer;-webkit-user-select:none;user-select:none;}" +
      ".loops-switch{width:38px;height:22px;border-radius:100px;background:rgba(13,42,82,.2);position:relative;transition:background .2s;}" +
      ".loops-switch::after{content:'';position:absolute;top:3px;left:3px;width:16px;height:16px;border-radius:50%;background:#fff;transition:left .2s;box-shadow:0 1px 3px rgba(0,0,0,.2);}" +
      ".loops-moretime.on{opacity:1;} .loops-moretime.on .loops-switch{background:var(--navy);} .loops-moretime.on .loops-switch::after{left:19px;}" +
      ".loops-paste-note{display:none;margin:-4px 0 10px;font-size:.82rem;font-weight:700;color:var(--red);text-align:center;}" +
      ".loops-paste-note.show{display:block;}" +
      ".loops-fb{margin-top:14px;padding:12px;border-radius:10px;font-weight:700;text-align:center;}" +
      ".loops-fb.good{background:#dcfce7;color:#166534;} .loops-fb.bad{background:#fee2e2;color:#991b1b;}" +
      ".loops-fb.mastered{background:#fef9c3;color:#854d0e;}" +
      ".loops-result{text-align:center;padding:10px 0;}" +
      // Results card — top-trumps style, framed in the category colour
      ".loops-card{width:272px;margin:4px auto 0;border-radius:20px;background:var(--catDeep);padding:7px;box-shadow:0 14px 30px rgba(13,42,82,.22);text-align:left;}" +
      ".loops-card-in{background:#fff;border-radius:14px;overflow:hidden;}" +
      ".loops-card-head{display:flex;justify-content:space-between;align-items:flex-start;gap:8px;padding:10px 12px 8px;}" +
      ".loops-card-title{font-family:'Playfair Display',serif;font-size:1.02rem;font-weight:700;line-height:1.15;color:var(--navy);display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden;}" +
      ".loops-card-loop{font-size:.72rem;font-weight:700;opacity:.65;margin-top:2px;}" +
      ".loops-card-level{flex-shrink:0;font-size:.68rem;font-weight:800;background:var(--catDeep);color:var(--catInk);border-radius:100px;padding:3px 9px;white-space:nowrap;}" +
      ".loops-card-art{height:112px;margin:0 10px;border-radius:10px;display:flex;align-items:center;justify-content:center;font-size:3rem;background:linear-gradient(135deg,var(--cat),var(--catWash));overflow:hidden;}" +
      ".loops-card-art img{width:100%;height:100%;object-fit:cover;display:block;}" +
      ".loops-card-stats{padding:8px 12px 4px;}" +
      ".loops-card-stat{display:flex;align-items:center;justify-content:space-between;padding:7px 4px;border-bottom:1px dashed #E7E3D8;font-size:.9rem;}" +
      ".loops-card-stat:last-child{border-bottom:none;}" +
      ".loops-card-stat .k{font-weight:700;} .loops-card-stat .v{font-weight:800;font-size:1rem;font-variant-numeric:tabular-nums;}" +
      ".loops-card-best{font-size:.6rem;font-weight:800;color:#9a6b12;background:#FDF3DF;border-radius:100px;padding:2px 6px;margin-left:6px;vertical-align:middle;}" +
      ".loops-card-foot{display:flex;justify-content:space-between;padding:8px 12px 10px;font-size:.64rem;font-weight:700;opacity:.55;letter-spacing:.04em;text-transform:uppercase;}" +
      ".loops-card-overlay{display:none;position:fixed;inset:0;background:rgba(13,42,82,.86);-webkit-backdrop-filter:blur(4px);backdrop-filter:blur(4px);z-index:210;align-items:center;justify-content:center;padding:20px;}" +
      ".loops-card-overlay.open{display:flex;} .loops-card-overlay-in{width:100%;max-width:300px;text-align:center;}" +
      ".loops-card-btn{margin-left:auto;flex-shrink:0;width:34px;height:34px;border-radius:100px;border:1.5px solid rgba(13,42,82,.18);background:#fff;font-size:1rem;cursor:pointer;display:inline-flex;align-items:center;justify-content:center;padding:0;}" +
      ".loops-ws-bar{display:flex;height:10px;border-radius:10px;background:#F1E4C4;overflow:hidden;margin-top:8px;}" +
      ".loops-ws-bar .old{background:#E0A93B;} .loops-ws-bar .new{background:#2FB18A;}" +
      ".loops-ws-pile{padding:8px 12px 0;font-size:.8rem;font-weight:800;color:var(--navy);}" +
      ".loops-ws-pile small{font-weight:600;opacity:.65;}" +
      ".loops-card.ws{background:#E0A93B;} .loops-card.ws .loops-card-stat .k{white-space:nowrap;margin-right:8px;}" +
      // Dublin encouragement: a yellow Post-it with a pressed Loops stamp. Sticks on, peels, falls away (1.4s).
      ".loops-toast{position:fixed;top:36%;left:50%;z-index:250;width:min(240px,72vw);min-height:150px;padding:24px 18px 18px;color:#0D2A52;font-weight:900;font-size:1.35rem;line-height:1.25;text-align:center;display:flex;align-items:center;justify-content:center;background:#FFE873;background-image:linear-gradient(180deg,#FFE04A 0,#FFEB80 18%,#FFF1A6 100%);box-shadow:0 18px 30px -8px rgba(13,42,82,.35);border-bottom-right-radius:30px 9px;pointer-events:none;opacity:0;transform-origin:50% 0;transform:translate(-50%,-50%) scale(.5) rotate(-10deg);}" +
      ".loops-toast.on{animation:loopsNote 1.4s forwards;}" +
      "@keyframes loopsNote{0%{opacity:0;transform:translate(-50%,-50%) scale(.5) rotate(-10deg);animation-timing-function:cubic-bezier(.2,.9,.3,1.3);}12%{opacity:1;transform:translate(-50%,-50%) scale(1.05) rotate(3deg);}20%{transform:translate(-50%,-50%) scale(1) rotate(-2deg);}58%{transform:translate(-50%,-50%) rotate(-2deg);animation-timing-function:ease-in;}66%{transform:translate(-50%,-50%) rotate(6deg);}74%{opacity:1;transform:translate(-50%,-50%) rotate(-4deg);animation-timing-function:cubic-bezier(.5,0,.9,.6);}100%{opacity:0;transform:translate(-30%,90vh) rotate(38deg);}}" +
      ".loops-stamp{position:absolute;right:-14px;bottom:-16px;width:78px;height:78px;transform:rotate(-14deg);opacity:.82;mix-blend-mode:multiply;pointer-events:none;}" +
      ".loops-stamp svg{width:100%;height:100%;display:block;}" +
      ".loops-cheer{position:relative;margin:14px auto 18px;max-width:280px;padding:20px 40px 18px 16px;color:#0D2A52;font-weight:900;font-size:1.15rem;line-height:1.3;background:#FFE873;background-image:linear-gradient(180deg,#FFE04A 0,#FFEB80 22%,#FFF1A6 100%);transform:rotate(-1.5deg);box-shadow:0 12px 22px -8px rgba(13,42,82,.3);border-bottom-right-radius:26px 8px;}" +
      ".loops-cheer .loops-stamp{width:58px;height:58px;right:-16px;bottom:-14px;}" +
      ".loops-send{display:inline-flex;align-items:center;gap:8px;margin:4px auto 6px;padding:11px 22px;border-radius:100px;border:none;background:#F3D250;color:#0D2A52;font-weight:900;font-size:.95rem;cursor:pointer;box-shadow:0 4px 0 #C9A21E,0 8px 18px rgba(13,42,82,.18);}" +
      ".loops-send:active{transform:translateY(2px);box-shadow:0 2px 0 #C9A21E;}" +
      ".loops-send:not(.loops-send-top) svg{width:17px;height:17px;}" +
      "button.loops-send-top{margin:4px auto 6px;border:none;cursor:pointer;font-family:inherit;}" +
      ".loops-send-top{margin-left:auto;display:inline-flex;align-items:center;gap:6px;padding:6px 14px;border-radius:100px;background:#F3D250;color:#0D2A52;text-decoration:none;font-weight:900;font-size:.85rem;box-shadow:0 3px 0 #C9A21E;}" +
      ".loops-card-hint{text-align:center;font-size:.78rem;opacity:.65;margin:12px 0 4px;}" +
      ".loops-result .big{font-size:2rem;font-weight:900;color:var(--navy);}" +
      ".loops-breakdown{text-align:left;margin-top:16px;max-height:280px;overflow-y:auto;border-radius:10px;}" +
      ".loops-bd-label{font-size:.78rem;font-weight:800;opacity:.6;margin-bottom:8px;}" +
      ".loops-bd-row{display:flex;gap:8px;padding:9px 10px;border-radius:8px;margin-bottom:6px;font-size:.83rem;line-height:1.35;}" +
      ".loops-bd-row.good{background:#dcfce7;color:#166534;}" +
      ".loops-bd-row.bad{background:#fee2e2;color:#991b1b;}" +
      ".loops-bd-icon{flex-shrink:0;font-weight:900;}" +
      ".loops-bd-q{font-weight:700;}" +
      ".loops-bd-detail{opacity:.85;margin-top:2px;}" +
      ".loops-bd-pill{display:inline-block;background:#dcfce7;color:#166534;border:1px solid #86efac;font-weight:800;padding:1px 8px;border-radius:100px;}" +
      ".loops-stack{display:flex;flex-direction:column;gap:10px;margin-top:16px;}" +
      ".loops-section-label{font-size:.78rem;text-transform:uppercase;letter-spacing:.06em;opacity:.55;font-weight:800;margin:18px 0 8px;}" +
      ".loops-ws-info{background:none;border:none;color:var(--navy);opacity:.55;font-size:14px;cursor:pointer;padding:0 0 0 4px;vertical-align:middle;}" +
      ".loops-ws-overlay{display:none;position:fixed;inset:0;background:rgba(13,42,82,.55);z-index:200;align-items:center;justify-content:center;padding:20px;}" +
      ".loops-ws-overlay.open{display:flex;}" +
      ".loops-ws-modal{background:#fff;border-radius:16px;max-width:340px;width:100%;padding:22px;text-align:center;}" +
      ".loops-ws-modal .emoji{font-size:2rem;margin-bottom:8px;}" +
      ".loops-ws-modal h3{font-family:'Playfair Display',serif;color:var(--navy);font-size:1.15rem;margin-bottom:10px;}" +
      ".loops-ws-modal p{font-size:.9rem;color:var(--navy);opacity:.85;line-height:1.5;margin-bottom:6px;}" +
      ".loops-ws-modal button{margin-top:14px;width:100%;padding:12px;border:none;border-radius:100px;background:var(--navy);color:#fff;font-weight:700;cursor:pointer;}";
    var style = document.createElement("style");
    style.id = "loopsEngineStyles";
    style.textContent = css;
    document.head.appendChild(style);
  }

  // ── REPORT A PROBLEM ──
  var LOOPS_REPORT_WORKER_URL = "https://dry-credit-f396.seansynge.workers.dev";
  var ICON_SHARE = '<svg viewBox="0 0 24 24" width="14" height="14" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 12v7a1 1 0 0 0 1 1h14a1 1 0 0 0 1-1v-7"/><path d="M12 3v12"/><path d="M7.5 7.5 12 3l4.5 4.5"/></svg>';

  // ── SEND ── share this game (or a card) with the phone's own share sheet;
  // on a computer, copy the link instead. Only the game's link and a line of
  // text are sent — scores stay on this phone.
  function gameLink() { return location.origin + location.pathname; }
  function sendLink(text, btn) {
    var url = gameLink();
    if (navigator.share) {
      navigator.share({ title: GAME.name + " · Loops", text: text, url: url }).catch(function () {});
      return;
    }
    var label = btn ? btn.innerHTML : "";
    function done() { if (btn) { btn.innerHTML = "✓ Link copied"; setTimeout(function () { btn.innerHTML = label; }, 1600); } }
    if (navigator.clipboard) navigator.clipboard.writeText(text + " " + url).then(done).catch(function () { prompt("Copy this link:", url); });
    else prompt("Copy this link:", url);
  }
  function sendCardBtn(text) {
    return '<button type="button" class="loops-send loops-send-top" data-send="' + escapeHtml(text) + '">' + ICON_SHARE + ' Share</button>';
  }

  function loopIndexFor(q) {
    if (G.mode === "loop") return G.loopIdx;
    var key = questionKey(q);
    for (var i = 0; i < QUESTION_INDEX.length; i++) {
      if (QUESTION_INDEX[i].key === key) return QUESTION_INDEX[i].loopIdx;
    }
    return null;
  }

  function renderReportButton(q) {
    var wrap = el("loopsReportWrap");
    wrap.innerHTML = "";
    addReportButton(wrap, GAME.slug, GAME.category, loopIndexFor(q), q.q, q.a, function () { return G.lastUserAnswer; });
  }

  function addReportButton(containerEl, gameId, category, loopIndex, questionText, correctAnswer, getUserAnswer) {
    var btn = document.createElement("button");
    btn.textContent = "Report a problem";
    btn.setAttribute("type", "button");
    btn.style.cssText = "background:none;border:none;color:#9AA2AD;font-size:11px;text-decoration:underline;padding:6px;margin-top:8px;cursor:pointer;";

    btn.addEventListener("click", function () {
      btn.disabled = true;
      btn.textContent = "Sending...";
      var userAnswer = null;
      try { userAnswer = getUserAnswer ? getUserAnswer() : null; } catch (e) {}

      sendReport(gameId, category, loopIndex, questionText, correctAnswer, userAnswer)
        .then(function () {
          btn.textContent = "Thanks - we will check it";
        })
        .catch(function () {
          btn.textContent = "Could not send - try later";
          btn.disabled = false;
        });
    });

    containerEl.appendChild(btn);
  }

  function sendReport(gameId, category, loopIndex, questionText, correctAnswer, userAnswer) {
    return fetch(LOOPS_REPORT_WORKER_URL + "/report", {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({
        gameId: gameId,
        category: category,
        loopIndex: loopIndex,
        questionText: questionText,
        correctAnswer: correctAnswer,
        userAnswer: userAnswer,
        note: ""
      })
    }).then(function (r) {
      if (!r.ok) throw new Error("report failed");
      return r.json();
    });
  }

  // ── SKELETON ──
  function buildSkeleton() {
    var root = el("loopsApp");
    root.innerHTML =
      '<div id="loopsToast" class="loops-toast" role="status" aria-live="polite"></div>' +
      '<div style="margin-bottom:10px;display:flex;gap:16px;align-items:center;">' +
      '<a href="../library.html" style="display:inline-flex;align-items:center;gap:4px;color:var(--navy);text-decoration:none;font-weight:700;font-size:.85rem;opacity:.75;">&larr; Library</a>' +
      '<a href="#" id="loopsLevelsLink" style="display:inline-flex;align-items:center;gap:4px;color:var(--navy);text-decoration:none;font-weight:700;font-size:.85rem;opacity:.75;">&#8962; Levels</a>' +
      '<a href="#" id="loopsSendGame" class="loops-send-top">' + ICON_SHARE + ' Share</a>' +
      '</div>' +
      '<div class="loops-header">' +
      '<img class="loops-logo-mark" src="' + (GAME.logoPath || "../Loops_triskel_mark.png") + '" alt="Loops" onerror="this.style.display=&#39;none&#39;">' +
      '<div style="font-size:2rem;">' + (GAME.emoji || "🎮") + '</div>' +
      "<h1>" + GAME.name + "</h1><div class=&#39;sub&#39;>Loops Learning Tools · Dublin</div></div>" +
      '<div id="loopsHome" class="loops-screen active">' +
      '<div id="loopsGrid" class="loops-grid"></div>' +
      '<div class="loops-moretime" id="loopsMoreTime" role="switch" aria-checked="false" tabindex="0"><span>⏱ Extra time</span><span class="loops-switch"></span></div>' +
      '<div class="loops-stack"><button class="loops-btn ghost" id="loopsResetBtn">Reset progress</button></div>' +
      "</div>" +
      '<div id="loopsPlay" class="loops-screen">' +
      '<div class="loops-meta-row"><span id="loopsQProg"></span><span id="loopsTimerLabel"></span></div>' +
      '<div class="loops-timerwrap"><div id="loopsTimerBar"></div></div>' +
      '<div class="loops-q-row"><div class="loops-q" id="loopsQText"></div>' +
      '<button class="loops-icon-btn" id="loopsSpeakBtn" type="button" title="Read aloud" aria-label="Read the question aloud" style="display:none;">' + ICON_SPEAKER + '</button></div>' +
      '<div id="loopsOptsWrap" class="loops-opts"></div>' +
      '<div id="loopsTypedWrap" style="display:none;">' +
      '<div class="loops-input-wrap"><input class="loops-input" id="loopsTypedInput" placeholder="Type your answer..." autocomplete="off" autocorrect="off" autocapitalize="off" spellcheck="false" />' +
      '<button class="loops-icon-btn" id="loopsMicBtn" type="button" title="Say your answer" aria-label="Say your answer" style="display:none;">' + ICON_MIC + '</button></div>' +
      '<div id="loopsPasteNote" class="loops-paste-note">Type it out — that&#39;s how it sticks ✍️</div>' +
      '<button class="loops-btn" id="loopsSubmitBtn">Submit</button></div>' +
      '<div id="loopsReportWrap" style="text-align:center;"></div>' +
      '<div id="loopsFb" class="loops-fb" style="display:none;"></div>' +
      '<button class="loops-btn" id="loopsNextBtn" style="display:none;margin-top:10px;">Next →</button>' +
      "</div>" +
      '<div id="loopsResult" class="loops-screen"><div class="loops-result">' +
      '<div id="loopsCheer" class="loops-cheer" style="display:none;"></div>' +
      '<div id="loopsResultTitle" style="font-size:1.2rem;font-weight:800;margin-bottom:8px;"></div>' +
      '<div id="loopsCard"></div>' +
      '<div class="big" id="loopsResultScore"></div>' +
      '<div style="font-size:1.1rem;font-weight:700;color:var(--navy);margin-top:6px;" id="loopsResultTime"></div>' +
      '<div id="loopsResultBreakdown" class="loops-breakdown"></div>' +
      '<div class="loops-stack"><button class="loops-btn" id="loopsNextLevelBtn" style="display:none;">Next level →</button>' +
      '<button class="loops-btn" id="loopsAgainBtn">Play again</button>' +
      '<button class="loops-btn ghost" id="loopsBackBtn">Back to loops</button></div>' +
      "</div></div>" +
      '<div class="loops-card-overlay" id="loopsCardOverlay"><div class="loops-card-overlay-in">' +
      '<div id="loopsCardOverlayBody"></div>' +
      '<div class="loops-card-hint" style="color:#fff;opacity:.85;">Hold it up — pick a stat. Highest wins (fastest for Speed).</div>' +
      '<button class="loops-btn ghost" id="loopsCardCloseBtn" style="background:#fff;margin-top:10px;">Close</button>' +
      '</div></div>' +
      '<div class="loops-ws-overlay" id="loopsWsOverlay"><div class="loops-ws-modal">' +
      '<div class="emoji">🎯</div>' +
      '<h3>What are Weak Spots?</h3>' +
      '<p>Any question you miss gets tracked here — from any loop, not just the one you were on.</p>' +
      '<p>Answer it right ' + MASTERY_TARGET + ' times (missing it doesn&#39;t reset the count) and it&#39;s marked mastered for good.</p>' +
      '<button id="loopsWsCloseBtn">Got it</button>' +
      '</div></div>';

    el("loopsWsCloseBtn").addEventListener("click", function () {
      el("loopsWsOverlay").classList.remove("open");
      try { localStorage.setItem("loops_seen_weakspots_intro", "1"); } catch (e) {}
    });

    // Answers must be typed, not pasted — pasting the answer shown after a
    // miss (or from anywhere else) skips the recall the game exists for.
    var typedInput = el("loopsTypedInput"), pasteNoteTimer = null;
    function blockInsert(e) {
      e.preventDefault();
      var note = el("loopsPasteNote");
      note.classList.add("show");
      clearTimeout(pasteNoteTimer);
      pasteNoteTimer = setTimeout(function () { note.classList.remove("show"); }, 2200);
    }
    typedInput.addEventListener("paste", blockInsert);
    typedInput.addEventListener("drop", blockInsert);
    typedInput.addEventListener("beforeinput", function (e) {
      if (e.inputType === "insertFromPaste" || e.inputType === "insertFromDrop" || e.inputType === "insertFromYank" || e.inputType === "insertFromPasteAsQuotation") blockInsert(e);
    });

    // Read aloud / voice answer — each only shown where the browser supports it.
    if (synth) { el("loopsSpeakBtn").style.display = ""; el("loopsSpeakBtn").addEventListener("click", speakQuestion); }
    if (SR) { el("loopsMicBtn").style.display = ""; el("loopsMicBtn").addEventListener("click", toggleMic); }

    // Extra time — doubles every question's clock. Remembered on this device only.
    var moreTime = el("loopsMoreTime");
    function paintMoreTime() {
      var on = timeFactor() > 1;
      moreTime.classList.toggle("on", on);
      moreTime.setAttribute("aria-checked", on ? "true" : "false");
    }
    function flipMoreTime() {
      try { localStorage.setItem("loops_more_time", timeFactor() > 1 ? "0" : "1"); } catch (e) {}
      paintMoreTime();
    }
    moreTime.addEventListener("click", flipMoreTime);
    moreTime.addEventListener("keydown", function (e) { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); flipMoreTime(); } });
    paintMoreTime();

    el("loopsCardCloseBtn").addEventListener("click", function () { el("loopsCardOverlay").classList.remove("open"); });
    el("loopsCardOverlay").addEventListener("click", function (e) { if (e.target === this) this.classList.remove("open"); });

    el("loopsResetBtn").addEventListener("click", function () {
      if (!confirm("Reset all progress for this game?")) return;
      save = { unlocked: 0, best: {}, bestScore: {}, mastery: {}, plays: {}, bestStreak: {}, ws: { rounds: 0, bestGain: 0, bestTime: 0, bestStreak: 0 } };
      persist();
      renderHome();
    });

    // Jump straight back to this game's level select from anywhere (mid-
    // question included) without leaving the page — no trip back through
    // the Library to find the same game again.
    document.addEventListener("pointerdown", hideToast, true);
    el("loopsSendGame").addEventListener("click", function (e) {
      e.preventDefault();
      sendLink("Try " + GAME.name + " on Loops — a free practice game 🎮", this);
    });
    // One handler for every "Send my card" button (results + saved cards).
    el("loopsApp").addEventListener("click", function (e) {
      var b = e.target && e.target.closest && e.target.closest(".loops-send");
      if (b) { e.stopPropagation(); sendLink(b.getAttribute("data-send"), b); }
    });
    el("loopsLevelsLink").addEventListener("click", function (e) {
      e.preventDefault();
      clearInterval(G.timer);
      renderHome();
    });
  }

  // ── HOME ──
  function renderHome() {
    stopSpeaking(); stopMic();
    show("loopsHome");
    var grid = el("loopsGrid");
    grid.innerHTML = "";

    var ws = weakSpots();
    if (ws.length > 0) {
      var wsTile = document.createElement("div");
      wsTile.className = "loops-tile weak";
      var pile = wsPile();
      wsTile.innerHTML =
        '<div class="loops-tile-top"><span>🎯</span><span>Weak Spots</span><span class="loops-badge">' + ws.length + '</span>' +
        '<button class="loops-ws-info" id="loopsWsInfoBtn" title="What is this?">ⓘ</button>' +
        (save.ws.rounds ? '<button class="loops-card-btn" id="loopsWsCardBtn" title="Show my card" aria-label="Show my best Weak Spots card">🃏</button>' : '') + '</div>' +
        '<div class="loops-tile-meta" style="opacity:.9;font-weight:700;">Your list: ' + pile.left + ' steps left of ' + pile.total + '</div>' +
        wsBarHtml(pile, 0) +
        '<div class="loops-tile-meta">Every right answer knocks one off. ' + MASTERY_TARGET + ' on a question and it&#39;s fixed for good.</div>' +
        '<div class="loops-tile-meta">Tap to chip away →</div>';
      wsTile.addEventListener("click", function (e) {
        if (e.target && e.target.id === "loopsWsInfoBtn") {
          el("loopsWsOverlay").classList.add("open");
          return;
        }
        if (e.target && e.target.id === "loopsWsCardBtn") { showWsBestCard(); return; }
        openReview(ws, "Weak Spots");
      });
      grid.appendChild(wsTile);

      var seenWsIntro = false;
      try { seenWsIntro = localStorage.getItem("loops_seen_weakspots_intro") === "1"; } catch (e) {}
      if (!seenWsIntro) {
        el("loopsWsOverlay").classList.add("open");
      }
    }

    GAME.loops.forEach(function (loop, idx) {
      var unlocked = idx <= save.unlocked;
      var best = save.best[idx];
      var bestScore = save.bestScore[idx];

      var tile = document.createElement("div");
      tile.className = "loops-tile " + (unlocked ? "" : "locked");
      tile.innerHTML =
        '<div class="loops-tile-top"><span>' + (loop.emoji || "🔹") + "</span><span>" + loop.name + "</span>" +
        (unlocked && best ? '<button class="loops-card-btn" data-card="' + idx + '" title="Show my card" aria-label="Show my best card for this level">🃏</button>' : "") +
        "</div>" +
        '<div class="loops-tile-meta">' + loop.qs.length + " questions · Best time: " + (best ? fmtTime(best) : "—") + "</div>" +
        '<div class="loops-tile-meta">High score: ' + (bestScore !== undefined ? (bestScore + "/" + loop.qs.length) : "—") + "</div>" +
        '<div class="loops-tile-meta">' + (unlocked ? "Tap to play →" : "🔒 Locked") + "</div>";
      if (unlocked) tile.addEventListener("click", function (e) {
        if (e.target && e.target.closest && e.target.closest(".loops-card-btn")) { showBestCard(idx); return; }
        openLoop(idx);
      });
      grid.appendChild(tile);

      // Halfway Check: appears once the halfway-point loop is complete,
      // wherever that actually falls for this game's loop count (not
      // hardcoded, since games can have 5 loops, 10, or otherwise).
      var halfwayIdx = Math.floor((GAME.loops.length - 1) / 2);
      if (idx === halfwayIdx && GAME.loops.length > 2 && save.unlocked > halfwayIdx) {
        var halfwaySpots = weakSpots().filter(function (item) { return item.loopIdx <= halfwayIdx; });
        var hwTile = document.createElement("div");
        hwTile.className = "loops-tile halfway";
        hwTile.innerHTML =
          '<div class="loops-tile-top"><span>⭐</span><span>Halfway Check</span></div>' +
          '<div class="loops-tile-meta">' + (halfwaySpots.length > 0
            ? "Halfway there already! Lock in a few from Loops 1–" + (halfwayIdx + 1) + " before the back half."
            : "Halfway there and everything from Loops 1–" + (halfwayIdx + 1) + " is rock solid. Great start.") + '</div>' +
          '<div class="loops-tile-meta">' + (halfwaySpots.length > 0 ? "Tap to review →" : "✓ All clear") + '</div>';
        if (halfwaySpots.length > 0) {
          hwTile.addEventListener("click", function () { openReview(halfwaySpots, "Halfway Check"); });
        } else {
          hwTile.style.cursor = "default";
        }
        grid.appendChild(hwTile);
      }
    });
  }

  function show(id) {
    document.querySelectorAll("#loopsApp .loops-screen").forEach(function (s) { s.classList.remove("active"); });
    el(id).classList.add("active");
  }

  // ── LOOP PLAY ──
  function openLoop(idx) {
    G.mode = "loop";
    G.loopIdx = idx;
    var loop = GAME.loops[idx];
    G.queue = shuffle(loop.qs);
    G.qi = 0; G.correct = 0; G.wrongs = 0; G.requeued = {}; G.seenKeys = {}; G.firstTryCorrect = 0; G.roundLog = [];
    G.cheers = 0; G.lastCheerQi = -9; G.run = 0; G.lastWasMiss = false;
    G.startMs = performance.now();
    G.pausedMs = 0;
    show("loopsPlay");
    toneStart();
    renderQuestion();
  }

  function openReview(items, label) {
    G.mode = "review";
    G.reviewLabel = label;
    G.wsGain = 0; G.wsFixed = 0;
    G.queue = shuffle(items.map(function (item) { return item.q; }));
    G.qi = 0; G.correct = 0; G.wrongs = 0; G.requeued = {}; G.seenKeys = {}; G.firstTryCorrect = 0; G.roundLog = [];
    G.cheers = 0; G.lastCheerQi = -9; G.run = 0; G.lastWasMiss = false;
    G.startMs = performance.now();
    G.pausedMs = 0;
    show("loopsPlay");
    toneStart();
    renderQuestion();
  }

  function renderQuestion() {
    var q = G.queue[G.qi];
    G.answered = false;
    G.lastUserAnswer = null;
    var timeLimit = (G.mode === "loop" ? (GAME.loops[G.loopIdx].timeLimit || 15) : 15) * timeFactor();
    G.spokenThisQ = false;
    stopSpeaking(); stopMic();
    el("loopsQProg").textContent = (G.qi + 1) + " / " + G.queue.length;
    el("loopsQText").textContent = q.q;
    el("loopsFb").style.display = "none";
    el("loopsNextBtn").style.display = "none";
    renderReportButton(q);

    if (q.type === "mc") {
      el("loopsOptsWrap").style.display = "flex";
      el("loopsTypedWrap").style.display = "none";
      var wrap = el("loopsOptsWrap");
      wrap.innerHTML = "";
      shuffle(q.opts || [q.a]).forEach(function (opt) {
        var b = document.createElement("button");
        b.className = "loops-opt";
        b.textContent = opt;
        b.addEventListener("click", function () { submitMC(opt, b); });
        wrap.appendChild(b);
      });
    } else {
      el("loopsOptsWrap").style.display = "none";
      el("loopsTypedWrap").style.display = "block";
      var inp = el("loopsTypedInput");
      inp.value = ""; inp.disabled = false;
      el("loopsSubmitBtn").onclick = submitTyped;
      inp.onkeydown = function (e) { if (e.key === "Enter") submitTyped(); };
      setTimeout(function () { inp.focus(); }, 50);
    }

    startTimer(timeLimit);
  }

  function startTimer(limit) {
    clearInterval(G.timer);
    G.paused = false;
    G.limit = limit;
    G.t = limit;
    updateBar(limit, limit);
    el("loopsTimerLabel").textContent = limit.toFixed(0) + "s";
    runTimer();
  }
  function runTimer() {
    clearInterval(G.timer);
    G.timer = setInterval(function () {
      G.t -= 0.1;
      updateBar(G.t, G.limit);
      el("loopsTimerLabel").textContent = Math.max(0, G.t).toFixed(1) + "s";
      if (G.t <= 0) { clearInterval(G.timer); timeUp(); }
    }, 100);
  }
  // Paused only while a question is being read aloud; the paused stretch is
  // also left out of the round's total time, so listening never costs a record.
  function pauseTimer() {
    if (G.answered || G.paused) return;
    clearInterval(G.timer);
    G.paused = true;
    G.pauseStart = performance.now();
  }
  function endPause() {
    if (!G.paused) return false;
    G.paused = false;
    G.pausedMs = (G.pausedMs || 0) + (performance.now() - G.pauseStart);
    return true;
  }
  function resumeTimer() {
    if (endPause() && !G.answered) runTimer();
  }

  // ── ACCESSIBILITY: read aloud, voice answers, extra time ──
  var LANG_TAGS = { en: "en-IE", es: "es-ES", fr: "fr-FR", de: "de-DE", ga: "ga-IE", it: "it-IT", pt: "pt-PT", nl: "nl-NL", pl: "pl-PL" };
  function langTag(code) { return LANG_TAGS[code] || code || "en-IE"; }
  function qLang() { return (GAME && GAME.lang && GAME.lang.q) || "en"; }
  function aLang() { return (GAME && GAME.lang && GAME.lang.a) || qLang(); }
  // Games store one question language and one answer language, but vocab
  // games run both ways ("What does 'el sol' mean in English?" vs "How do
  // you say 'rain' in Spanish?"). Naming the question language (and not the
  // answer language) flips that question's answers to the question language.
  var LANG_NAMES = {
    en: /\benglish\b|inglés|\banglais\b|\benglisch\b|béarla/i,
    es: /\bspanish\b|español|\bespanol\b|\bcastellano\b/i,
    fr: /\bfrench\b|français|\bfrancais\b/i,
    de: /\bgerman\b|\bdeutsch\b/i,
    ga: /\birish\b|\bgaeilge\b/i,
    it: /\bitalian\b|\bitaliano\b/i,
    pt: /\bportuguese\b|português/i,
    nl: /\bdutch\b/i,
    pl: /\bpolish\b/i
  };
  function answerLangFor(q) {
    var ql = qLang(), al = aLang();
    if (ql === al || !q) return al;
    var text = q.q || "";
    var namesQ = LANG_NAMES[ql] && LANG_NAMES[ql].test(text);
    var namesA = LANG_NAMES[al] && LANG_NAMES[al].test(text);
    return namesQ && !namesA ? ql : al;
  }
  // Splits a question so a quoted word/phrase is read in its own language:
  // the quoted bit is whichever language the answer ISN'T in.
  function questionParts(q) {
    var ql = qLang(), al = aLang(), ans = answerLangFor(q);
    var quoteLang = ans === al ? ql : al;
    if (ql === al || quoteLang === ql || !voiceFor(quoteLang)) return [{ text: q.q, code: ql }];
    var parts = [], re = /["\u201C\u00AB]([^"\u201D\u00BB]+)["\u201D\u00BB]/g, last = 0, m;
    while ((m = re.exec(q.q))) {
      if (m.index > last) parts.push({ text: q.q.slice(last, m.index), code: ql });
      parts.push({ text: m[1], code: quoteLang });
      last = re.lastIndex;
    }
    if (last < q.q.length) parts.push({ text: q.q.slice(last), code: ql });
    return parts.filter(function (p) { return /\S/.test(p.text); });
  }

  function timeFactor() {
    try { return localStorage.getItem("loops_more_time") === "1" ? 2 : 1; } catch (e) { return 1; }
  }

  var synth = window.speechSynthesis || null;
  var SR = window.SpeechRecognition || window.webkitSpeechRecognition || null;
  if (synth && synth.getVoices) synth.getVoices(); // starts the voice list loading early

  function voiceFor(code) {
    if (!synth) return null;
    var voices = synth.getVoices() || [];
    var tag = langTag(code).toLowerCase(), loose = null;
    for (var i = 0; i < voices.length; i++) {
      var vl = (voices[i].lang || "").toLowerCase().replace("_", "-");
      if (vl === tag) return voices[i];
      if (!loose && vl.split("-")[0] === code) loose = voices[i];
    }
    return loose;
  }

  var speakSession = 0;
  function stopSpeaking() {
    speakSession++;
    if (synth) synth.cancel();
    var b = el("loopsSpeakBtn");
    if (b) b.classList.remove("active");
  }
  function speakQuestion() {
    var q = G.queue[G.qi];
    if (!synth || !q) return;
    if (synth.speaking) { stopSpeaking(); resumeTimer(); return; } // tap again to stop

    var parts = questionParts(q);
    // Options are read in this question's answer language — only when the
    // phone actually has a voice for it, so options never come out mangled.
    var optLang = answerLangFor(q);
    if (q.type === "mc" && (optLang === qLang() || voiceFor(optLang))) {
      Array.prototype.forEach.call(document.querySelectorAll(".loops-opt"), function (b) {
        parts.push({ text: b.textContent, code: optLang });
      });
    }

    // First listen per question stops the clock; replays don't (so the
    // timer can't be frozen by tapping repeatedly).
    var pause = !G.answered && !G.spokenThisQ;
    G.spokenThisQ = true;
    if (pause) pauseTimer();

    var session = ++speakSession;
    var btn = el("loopsSpeakBtn");
    btn.classList.add("active");
    parts.forEach(function (p, i) {
      var u = new SpeechSynthesisUtterance(p.text);
      u.lang = langTag(p.code);
      var v = voiceFor(p.code);
      if (v) u.voice = v;
      u.rate = 0.95;
      if (i === parts.length - 1) {
        u.onend = u.onerror = function () {
          if (session !== speakSession) return;
          btn.classList.remove("active");
          if (pause) resumeTimer();
        };
      }
      synth.speak(u);
    });
  }

  // Voice answer: fills the box with what was heard — never auto-submits,
  // so the answer is still checked and sent by the player.
  var recog = null;
  function stopMic() {
    if (recog) { try { recog.abort(); } catch (e) {} recog = null; }
    var b = el("loopsMicBtn");
    if (b) b.classList.remove("listening");
  }
  function toggleMic() {
    if (!SR) return;
    if (recog) { try { recog.stop(); } catch (e) {} return; }
    var inp = el("loopsTypedInput");
    if (inp.disabled) return;
    var btn = el("loopsMicBtn");
    var r;
    try { r = new SR(); } catch (e) { return; }
    recog = r;
    r.lang = langTag(answerLangFor(G.queue[G.qi]));
    r.interimResults = true;
    r.continuous = false;
    r.maxAlternatives = 1;
    r.onstart = function () { btn.classList.add("listening"); };
    r.onresult = function (e) {
      if (inp.disabled) return;
      var t = "";
      for (var i = 0; i < e.results.length; i++) t += e.results[i][0].transcript;
      inp.value = t.trim().replace(/[.!?¡¿。]+$/g, "").replace(/^[¡¿]+/, "");
    };
    r.onerror = function (e) {
      // No permission, or no recogniser for this language on this device:
      // hide the mic rather than leave a button that can't work.
      if (e.error === "not-allowed" || e.error === "service-not-allowed" || e.error === "language-not-supported") btn.style.display = "none";
    };
    r.onend = function () { btn.classList.remove("listening"); if (recog === r) recog = null; };
    try { r.start(); } catch (e) { recog = null; btn.classList.remove("listening"); }
  }
  function updateBar(t, limit) {
    var pct = Math.max(0, (t / limit) * 100);
    var bar = el("loopsTimerBar");
    bar.style.width = pct + "%";
    bar.style.background = pct < 25 ? "#c94c4c" : pct < 50 ? "#c9a84c" : "var(--catDeep)";
  }

  function timeUp() {
    if (G.answered) return;
    G.answered = true;
    G.lastUserAnswer = null;
    toneBad();
    var q = G.queue[G.qi];
    if (q.type === "mc") {
      document.querySelectorAll(".loops-opt").forEach(function (b) {
        if (b.textContent === q.a) b.classList.add("correct"); else b.classList.add("faded");
        b.disabled = true;
      });
    } else {
      el("loopsTypedInput").disabled = true;
    }
    handleResult(false, q, "⏱ Time's up");
  }

  function requeue(q) {
    var key = questionKey(q);
    if (!G.requeued[key]) {
      G.requeued[key] = true;
      G.queue.push(q);
    }
  }

  function submitMC(choice, btn) {
    if (G.answered) return;
    G.answered = true;
    G.lastUserAnswer = choice;
    clearInterval(G.timer);
    var q = G.queue[G.qi];
    var ok = choice === q.a;
    document.querySelectorAll(".loops-opt").forEach(function (b) {
      b.disabled = true;
      if (b.textContent === q.a) b.classList.add("correct");
      else if (b === btn && !ok) b.classList.add("wrong");
      else b.classList.add("faded");
    });
    handleResult(ok, q);
  }

  function submitTyped() {
    if (G.answered) return;
    G.answered = true;
    clearInterval(G.timer);
    var q = G.queue[G.qi];
    var inp = el("loopsTypedInput");
    inp.disabled = true;
    G.lastUserAnswer = inp.value;
    var match = matchTyped(inp.value, q.a);
    handleResult(match.correct, q, q.a, match.exact ? null : inp.value);
  }

  function handleResult(ok, q, correctAnswerLabel, nearMissInput) {
    stopSpeaking(); stopMic(); endPause();
    G.answeredCount = (G.answeredCount || 0) + 1;
    var key = questionKey(q);
    var isFirstAttempt = !G.seenKeys[key];
    if (isFirstAttempt) G.seenKeys[key] = true;

    var justMastered = false;

    if (ok) {
      G.correct++;
      if (isFirstAttempt) G.firstTryCorrect++;
      toneGood();
      if (save.mastery[key] !== undefined && save.mastery[key] < MASTERY_TARGET) {
        save.mastery[key] = Math.min(MASTERY_TARGET, save.mastery[key] + 1);
        if (save.mastery[key] === MASTERY_TARGET) justMastered = true;
        persist();
        if (isWsRound()) { G.wsGain = (G.wsGain || 0) + 1; if (justMastered) G.wsFixed = (G.wsFixed || 0) + 1; }
      }
    } else {
      G.wrongs++;
      toneBad();
      if (save.mastery[key] === undefined) {
        save.mastery[key] = 0; // starts haunting from the first miss
        persist();
      }
      requeue(q);
    }

    if (G.roundLog) {
      G.roundLog.push({ q: q.q, given: G.lastUserAnswer, correctAnswer: q.a, ok: ok });
    }

    if (justMastered) {
      toneMastered();
      showFeedback(true, q, "🌟 Mastered! That's " + MASTERY_TARGET + " for " + MASTERY_TARGET + " — it's yours now.", true);
    } else if (ok && nearMissInput) {
      showFeedback(true, q, "✔ Correct — close enough on the spelling: " + diffHighlight(nearMissInput, q.a), false, true);
    } else if (ok && isWsRound() && save.mastery[questionKey(q)] !== undefined) {
      showFeedback(true, q, pick(CORRECT_PHRASES) + "  +1 · " + save.mastery[questionKey(q)] + "/" + MASTERY_TARGET);
    } else {
      showFeedback(ok, q, ok ? pick(CORRECT_PHRASES) : (pick(WRONG_PHRASES) + " — " + q.a + ". You'll get it."));
    }
    if (!justMastered) maybeCheer(ok);
  }
  function isWsRound() { return G.mode === "review" && G.reviewLabel === "Weak Spots"; }

  function showFeedback(ok, q, msg, mastered, isHtml) {
    var fb = el("loopsFb");
    fb.className = "loops-fb " + (mastered ? "mastered" : (ok ? "good" : "bad"));
    if (isHtml) { fb.innerHTML = msg; } else { fb.textContent = msg; }
    fb.style.display = "block";
    var nextBtn = el("loopsNextBtn");
    nextBtn.style.display = "block";
    nextBtn.onclick = nextQuestion;
    // On a long question (lots of MC options, small screen) the button can
    // land below the fold — get it into view automatically so play isn't
    // slowed down by a manual scroll every question.
    try { nextBtn.scrollIntoView({ behavior: "smooth", block: "nearest" }); } catch (e) {}
  }

  function nextQuestion() {
    G.qi++;
    if (G.qi >= G.queue.length) { finishRound(); }
    else { renderQuestion(); }
  }

  function flushAnsweredStat() {
    var n = G.answeredCount || 0;
    G.answeredCount = 0;
    if (n === 0) return;
    try {
      fetch(LOOPS_REPORT_WORKER_URL + "/stats/answered", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ count: n })
      }).catch(function () {});
    } catch (e) {}
  }

  function escapeHtml(s) {
    return (s === null || s === undefined ? "" : String(s))
      .replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
  }

  function renderBreakdown(log) {
    var wrap = el("loopsResultBreakdown");
    if (!log || log.length === 0) { wrap.innerHTML = ""; return; }
    var html = '<div class="loops-bd-label">Here&#39;s how that round went — nice work getting through it 👇</div>';
    for (var i = 0; i < log.length; i++) {
      var row = log[i];
      var cls = row.ok ? "good" : "bad";
      var icon = row.ok ? "✔" : "✘";
      html += '<div class="loops-bd-row ' + cls + '">' +
        '<span class="loops-bd-icon">' + icon + '</span>' +
        '<div><div class="loops-bd-q">' + escapeHtml(row.q) + '</div>';
      if (row.ok) {
        var givenOk = row.given ? escapeHtml(row.given) : escapeHtml(row.correctAnswer);
        html += '<div class="loops-bd-detail">You said: ' + givenOk + ' — <span class="loops-bd-pill">' + escapeHtml(row.correctAnswer) + '</span> — nice one!</div>';
      } else {
        var given = row.given ? escapeHtml(row.given) : "No answer";
        html += '<div class="loops-bd-detail">You said: ' + given + ' — <span class="loops-bd-pill">' + escapeHtml(row.correctAnswer) + '</span>. You&#39;ll get it next time.</div>';
      }
      html += '</div></div>';
    }
    wrap.innerHTML = html;
  }

  function finishRound() {
    clearInterval(G.timer);
    flushAnsweredStat();
    var elapsed = (performance.now() - G.startMs - (G.pausedMs || 0)) / 1000;

    if (isWsRound()) { finishWsRound(elapsed); return; }
    if (G.mode === "review") {
      renderBreakdown(G.roundLog);
      show("loopsResult");
      el("loopsNextLevelBtn").style.display = "none";
      el("loopsAgainBtn").className = "loops-btn";
      el("loopsResultTitle").textContent = "✓ Review complete — great effort";
      setCheerBanner("review");
      el("loopsCard").innerHTML = "";
      el("loopsResultScore").style.display = "";
      el("loopsResultTime").style.display = "";
      el("loopsResultTime").textContent = fmtTime(elapsed);
      var remaining = weakSpots().length;
      el("loopsResultScore").textContent = remaining > 0
        ? "You're chipping away at it — " + remaining + " question" + (remaining === 1 ? "" : "s") + " left to master."
        : "🌟 Everything's mastered. That's the whole pool cleared — brilliant work.";
      toneWin();
      if (remaining === 0) confetti();
      el("loopsAgainBtn").onclick = function () { openReview(weakSpots(), G.reviewLabel); };
      el("loopsAgainBtn").style.display = weakSpots().length > 0 ? "block" : "none";
      el("loopsBackBtn").onclick = renderHome;
      return;
    }

    // mode === "loop"
    var totalQs = GAME.loops[G.loopIdx].qs.length;
    var oldBest = save.best[G.loopIdx];
    var isNewBestTime = !oldBest || elapsed < oldBest;
    if (isNewBestTime) save.best[G.loopIdx] = elapsed;

    var oldScore = save.bestScore[G.loopIdx];
    var isNewBestScore = oldScore === undefined || G.firstTryCorrect > oldScore;
    if (isNewBestScore) save.bestScore[G.loopIdx] = G.firstTryCorrect;

    save.plays[G.loopIdx] = (save.plays[G.loopIdx] || 0) + 1;
    var roundStreak = longestStreak(G.roundLog);
    if (!(save.bestStreak[G.loopIdx] >= roundStreak)) save.bestStreak[G.loopIdx] = roundStreak;

    if (save.unlocked === G.loopIdx && G.loopIdx < GAME.loops.length - 1) {
      save.unlocked = G.loopIdx + 1; // finishing unlocks the next loop regardless of mistakes
    }
    persist();

    renderBreakdown(G.roundLog);
    show("loopsResult");
    el("loopsResultTitle").textContent = isNewBestTime ? "🏆 New best time! Brilliant." : "🎉 Loop complete — well done!";
    var allDone = G.loopIdx === GAME.loops.length - 1 && GAME.loops.every(function (l, i) { return save.best[i]; });
    var ratio = G.firstTryCorrect / totalQs;
    setCheerBanner(allDone ? "all" : ratio === 1 ? "perfect" : (isNewBestScore && oldScore !== undefined) ? "pb" :
      ratio >= 0.7 ? "strong" : ratio >= 0.4 ? "middle" : "tough");
    el("loopsResultTime").textContent = fmtTime(elapsed);
    el("loopsResultScore").textContent = "Score: " + G.firstTryCorrect + "/" + totalQs + (isNewBestScore ? " — new high score!" : "") +
      (G.wrongs === 0 ? " — clean run, nice." : "");
    el("loopsResultScore").style.display = "none";
    el("loopsResultTime").style.display = "none";
    renderCard({
      elapsed: elapsed,
      score: G.firstTryCorrect,
      total: totalQs,
      bestTime: isNewBestTime && oldBest !== undefined,
      bestScore: isNewBestScore && oldScore !== undefined
    });
    toneWin();
    if (isNewBestTime || isNewBestScore) confetti();

    el("loopsAgainBtn").style.display = "block";
    el("loopsAgainBtn").onclick = function () { openLoop(G.loopIdx); };
    el("loopsBackBtn").onclick = renderHome;

    var nextBtn = el("loopsNextLevelBtn");
    var hasNext = G.loopIdx < GAME.loops.length - 1;
    if (hasNext) {
      nextBtn.style.display = "block";
      nextBtn.textContent = "Next level: " + (GAME.loops[G.loopIdx + 1].emoji || "🔹") + " " + GAME.loops[G.loopIdx + 1].name + " →";
      nextBtn.onclick = function () { openLoop(G.loopIdx + 1); };
      // Next level is the headline action here, so play-again steps back
      // to a secondary/ghost treatment rather than competing for attention.
      el("loopsAgainBtn").className = "loops-btn ghost";
    } else {
      nextBtn.style.display = "none";
      el("loopsAgainBtn").className = "loops-btn";
    }
  }

  // ── RESULTS CARD ── a top-trumps style card for the yard: same game, same
  // loop, one calls a stat, higher wins (faster wins on Speed). Everything on
  // it lives on this phone only.
  function longestStreak(log) {
    var best = 0, run = 0;
    (log || []).forEach(function (r) { run = r.ok ? run + 1 : 0; if (run > best) best = run; });
    return best;
  }
  function masteredCount() {
    var n = 0;
    for (var k in save.mastery) if (save.mastery[k] >= MASTERY_TARGET) n++;
    return n;
  }
  function renderCard(r) {
    el("loopsCard").innerHTML = cardHtml({
      loopIdx: G.loopIdx,
      speed: fmtTime(r.elapsed), bestTime: r.bestTime,
      score: r.score + "/" + r.total, bestScore: r.bestScore,
      streak: longestStreak(G.roundLog),
      grit: save.plays[G.loopIdx] || 1,
      foot: new Date().toLocaleDateString("en-IE", { day: "numeric", month: "short" })
    }) + '<div class="loops-card-hint">Hold it up — pick a stat. Highest wins (fastest for Speed).</div>' +
      '<div style="text-align:center;">' + sendCardBtn("I got " + r.score + "/" + r.total + " in " + fmtTime(r.elapsed) + " on Level " + (G.loopIdx + 1) + " of " + GAME.name + " on Loops 💪 Beat that:") + '</div>';
  }

  // His best for one level, pulled from this phone — no replay needed.
  function showBestCard(idx) {
    var loop = GAME.loops[idx];
    var hasStreak = save.bestStreak[idx] !== undefined;
    el("loopsCardOverlayBody").innerHTML = cardHtml({
      loopIdx: idx,
      speed: fmtTime(save.best[idx]), bestTime: false,
      score: (save.bestScore[idx] !== undefined ? save.bestScore[idx] : 0) + "/" + loop.qs.length, bestScore: false,
      streak: hasStreak ? save.bestStreak[idx] : "—",
      grit: save.plays[idx] || 1,
      foot: "Your best"
    }) + '<div style="text-align:center;margin-top:12px;">' + sendCardBtn("My best on Level " + (idx + 1) + " of " + GAME.name + ": " +
      (save.bestScore[idx] !== undefined ? save.bestScore[idx] : 0) + "/" + loop.qs.length + " in " + fmtTime(save.best[idx]) + " 💪 Beat that:") + '</div>';
    el("loopsCardOverlay").classList.add("open");
  }

  function cardHtml(d) {
    var loop = GAME.loops[d.loopIdx];
    var art = GAME.background
      ? '<img src="' + escapeHtml(GAME.background) + '" alt="" onerror="this.parentNode.textContent=&#39;' + escapeHtml(GAME.emoji || "🎮") + '&#39;">'
      : escapeHtml(GAME.emoji || "🎮");
    var best = '<span class="loops-card-best">BEST</span>';
    function stat(k, v, isBest) {
      return '<div class="loops-card-stat"><span class="k">' + k + '</span><span class="v">' + v + (isBest ? best : "") + "</span></div>";
    }
    return '<div class="loops-card"><div class="loops-card-in">' +
        '<div class="loops-card-head"><div><div class="loops-card-title">' + escapeHtml(GAME.name) + '</div>' +
          '<div class="loops-card-loop">' + escapeHtml((loop.emoji || "🔹") + " " + loop.name) + "</div></div>" +
          '<div class="loops-card-level">Level ' + (d.loopIdx + 1) + "</div></div>" +
        '<div class="loops-card-art">' + art + "</div>" +
        '<div class="loops-card-stats">' +
          stat("⚡ Speed", d.speed, d.bestTime) +
          stat("🎯 Score", d.score, d.bestScore) +
          stat("🌟 Streak", d.streak, false) +
          stat("🧠 Mastered", masteredCount(), false) +
          stat("🔥 Grit", d.grit, false) +
        "</div>" +
        '<div class="loops-card-foot"><span>Loops · Dublin</span><span>' + escapeHtml(d.foot) + "</span></div>" +
      "</div></div>";
  }

  // ── WEAK SPOTS FINISH + CARD ── leads with what they knocked off their
  // list, never with what's left. Levels, Halfway Check untouched.
  function finishWsRound(elapsed) {
    var gain = G.wsGain || 0, streak = longestStreak(G.roundLog);
    save.ws.rounds = (save.ws.rounds || 0) + 1;
    var newGain = gain > (save.ws.bestGain || 0);
    var newTime = !save.ws.bestTime || elapsed < save.ws.bestTime;
    if (newGain) save.ws.bestGain = gain;
    if (newTime) save.ws.bestTime = elapsed;
    if (streak > (save.ws.bestStreak || 0)) save.ws.bestStreak = streak;
    persist();
    var pile = wsPile();
    renderBreakdown(G.roundLog);
    show("loopsResult");
    el("loopsNextLevelBtn").style.display = "none";
    el("loopsAgainBtn").className = "loops-btn";
    setCheerBanner("review");
    el("loopsResultTitle").textContent = pile.left === 0
      ? "🌟 Your whole list is fixed. Brilliant."
      : gain > 0 ? "You knocked " + gain + " off your list 💪" : "Round done. Every go counts 💪";
    el("loopsResultScore").style.display = "none";
    el("loopsResultTime").style.display = "none";
    el("loopsCard").innerHTML = wsCardHtml({
      gain: gain, pile: pile, streak: streak, speed: fmtTime(elapsed), grit: save.ws.rounds,
      bestGain: newGain && save.ws.rounds > 1, bestTime: newTime && save.ws.rounds > 1,
      foot: new Date().toLocaleDateString("en-IE", { day: "numeric", month: "short" })
    }) + '<div class="loops-card-hint">Hold it up — pick a stat. Highest wins (fastest for Speed).</div>' +
      '<div style="text-align:center;">' + sendCardBtn("I knocked " + gain + " off my Weak Spots list in " + GAME.name + " on Loops 💪 Your turn:") + '</div>';
    toneWin();
    if (pile.left === 0 || newGain) confetti();
    el("loopsAgainBtn").textContent = "Keep chipping away";
    el("loopsAgainBtn").onclick = function () { el("loopsAgainBtn").textContent = "Play again"; openReview(weakSpots(), "Weak Spots"); };
    el("loopsAgainBtn").style.display = weakSpots().length > 0 ? "block" : "none";
    el("loopsBackBtn").onclick = function () { el("loopsAgainBtn").textContent = "Play again"; renderHome(); };
  }
  function showWsBestCard() {
    el("loopsCardOverlayBody").innerHTML = wsCardHtml({
      gain: save.ws.bestGain || 0, pile: wsPile(), streak: save.ws.bestStreak || 0,
      speed: save.ws.bestTime ? fmtTime(save.ws.bestTime) : "—", grit: save.ws.rounds || 0,
      best: true, foot: "Your best"
    }) + '<div style="text-align:center;margin-top:12px;">' + sendCardBtn("My best Weak Spots round in " + GAME.name + " on Loops: knocked " + (save.ws.bestGain || 0) + " off my list 💪 Your turn:") + '</div>';
    el("loopsCardOverlay").classList.add("open");
  }
  function wsCardHtml(d) {
    var art = GAME.background
      ? '<img src="' + escapeHtml(GAME.background) + '" alt="" onerror="this.parentNode.textContent=&#39;🎯&#39;">'
      : "🎯";
    var bestTag = '<span class="loops-card-best">BEST</span>';
    function stat(k, v, isBest) {
      return '<div class="loops-card-stat"><span class="k">' + k + '</span><span class="v">' + v + (isBest ? bestTag : "") + "</span></div>";
    }
    var fixed = masteredCount();
    return '<div class="loops-card ws"><div class="loops-card-in">' +
        '<div class="loops-card-head"><div><div class="loops-card-title">' + escapeHtml(GAME.name) + '</div>' +
          '<div class="loops-card-loop">🎯 Weak Spots</div></div>' +
          '<div class="loops-card-level" style="background:#E0A93B;color:#3d2a06;">Your list</div></div>' +
        '<div class="loops-card-art" style="height:88px;">' + art + "</div>" +
        '<div class="loops-ws-pile">📉 ' + d.pile.left + ' left <small>of ' + d.pile.total + ' steps</small>' +
          wsBarHtml(d.pile, d.best ? 0 : d.gain) + "</div>" +
        '<div class="loops-card-stats">' +
          stat("🪓 Knocked off", (d.gain > 0 ? "−" + d.gain : "0"), d.bestGain) +
          stat("🔧 Fixed", fixed > 0 ? fixed : '<span style="font-size:.74rem;font-weight:700;opacity:.75;white-space:nowrap;">Not yet · chipping away</span>', false) +
          stat("🔥 Comeback", d.streak, false) +
          stat("⚡ Speed", d.speed, d.bestTime) +
          stat("💪 Grit", d.grit, false) +
        "</div>" +
        '<div class="loops-card-foot"><span>Loops · Dublin</span><span>' + escapeHtml(d.foot) + "</span></div>" +
      "</div></div>";
  }

  function pingPlayerSeenOnce() {
    try {
      if (localStorage.getItem("loops_player_seen") === "1") return;
      var id = localStorage.getItem("loops_player_id");
      if (!id) {
        id = "p_" + Date.now().toString(36) + "_" + Math.random().toString(36).slice(2, 10);
        localStorage.setItem("loops_player_id", id);
      }
      fetch(LOOPS_REPORT_WORKER_URL + "/stats/seen", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ playerId: id })
      }).then(function () {
        localStorage.setItem("loops_player_seen", "1");
      }).catch(function () {}); // if it fails, we just try again next visit - no flag set
    } catch (e) {}
  }

  // Records this game as most-recently-played in a shared, same-origin
  // localStorage key. Read back by library.html (same domain — games/*.html
  // and library.html both live in this repo) to render a "Recently played"
  // row without the player having to search for the game again.
  function recordRecentlyPlayed() {
    try {
      var key = "loops_recently_played";
      var raw = localStorage.getItem(key);
      var arr = raw ? JSON.parse(raw) : [];
      if (!Array.isArray(arr)) arr = [];
      arr = arr.filter(function (r) { return r && r.slug !== GAME.slug; });
      arr.unshift({ slug: GAME.slug, ts: Date.now() });
      localStorage.setItem(key, JSON.stringify(arr.slice(0, 12)));
    } catch (e) {}
  }

  // ── INIT ──
  window.LoopsEngine = {
    init: function (gameData) {
      try {
        GAME = gameData;
        if (!GAME || !GAME.loops || !GAME.loops.length) throw new Error("This game has no playable content.");
        loadSave();
        buildQuestionIndex();
        injectStyles();
        syncCategoryFromLibrary();
        buildSkeleton();
        renderHome();
        pingPlayerSeenOnce();
        recordRecentlyPlayed();
      } catch (err) {
        var root = document.getElementById("loopsApp");
        if (root) {
          root.innerHTML =
            '<div style="max-width:420px;margin:40px auto;text-align:center;font-family:system-ui,sans-serif;padding:24px;">' +
            '<div style="font-size:2rem;margin-bottom:10px;">⚠️</div>' +
            '<div style="font-weight:800;font-size:1.1rem;margin-bottom:8px;">This game hit a snag loading</div>' +
            '<div style="opacity:.7;font-size:.9rem;">If you just got here from a fresh link, this can take a minute to go live — try refreshing. If it keeps happening, let whoever made this game know.</div>' +
            "</div>";
        }
        if (window.console) console.error("LoopsEngine failed to init:", err);
      }
    }
  };
})();
