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

  function injectStyles() {
    if (document.getElementById("loopsEngineStyles")) return;
    var cat = categoryColors();
    var css = "" +
      "#loopsApp{--navy:#0D2A52;--cat:" + cat.pastel + ";--catDeep:" + cat.deep + ";--catWash:" + cat.wash + ";--amber:" + AMBER + ";--ink:#0D2A52;--red:#c94c4c;" +
      "font-family:'Inter',system-ui,-apple-system,Segoe UI,Roboto,sans-serif;color:var(--ink);max-width:520px;margin:0 auto;padding:16px;" +
      "background:var(--catWash);border-radius:20px;}" +
      ".loops-screen{display:none;} .loops-screen.active{display:block;}" +
      ".loops-header{text-align:center;margin-bottom:18px;} .loops-header h1{font-family:'Playfair Display',serif;font-size:1.5rem;margin:6px 0 2px;}" +
      ".loops-header .sub{opacity:.7;font-size:.9rem;}" +
      ".loops-header .loops-logo-mark{height:36px;width:auto;border-radius:5px;margin-bottom:4px;}" +
      ".loops-grid{display:grid;gap:12px;}" +
      ".loops-tile{background:#fff;border:2px solid transparent;border-radius:14px;padding:16px;cursor:pointer;transition:.15s;box-shadow:0 4px 14px rgba(13,42,82,.1);}" +
      ".loops-tile.locked{opacity:.55;cursor:not-allowed;}" +
      ".loops-tile:not(.locked):hover{border-color:var(--catDeep);transform:translateY(-2px);}" +
      ".loops-tile.weak{border-color:var(--amber);background:#fffbea;}" +
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
      ".loops-fb{margin-top:14px;padding:12px;border-radius:10px;font-weight:700;text-align:center;}" +
      ".loops-fb.good{background:#dcfce7;color:#166534;} .loops-fb.bad{background:#fee2e2;color:#991b1b;}" +
      ".loops-fb.mastered{background:#fef9c3;color:#854d0e;}" +
      ".loops-result{text-align:center;padding:10px 0;}" +
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
      '<div style="margin-bottom:10px;"><a href="../library.html" style="display:inline-flex;align-items:center;gap:4px;color:var(--navy);text-decoration:none;font-weight:700;font-size:.85rem;opacity:.75;">&larr; Library</a></div>' +
      '<div class="loops-header">' +
      '<img class="loops-logo-mark" src="' + (GAME.logoPath || "../Loops_triskel_mark.png") + '" alt="Loops" onerror="this.style.display=&#39;none&#39;">' +
      '<div style="font-size:2rem;">' + (GAME.emoji || "🎮") + '</div>' +
      "<h1>" + GAME.name + "</h1><div class=&#39;sub&#39;>Loops Learning Tools · Dublin</div></div>" +
      '<div id="loopsHome" class="loops-screen active">' +
      '<div id="loopsGrid" class="loops-grid"></div>' +
      '<div class="loops-stack"><button class="loops-btn ghost" id="loopsResetBtn">Reset progress</button></div>' +
      "</div>" +
      '<div id="loopsPlay" class="loops-screen">' +
      '<div class="loops-meta-row"><span id="loopsQProg"></span><span id="loopsTimerLabel"></span></div>' +
      '<div class="loops-timerwrap"><div id="loopsTimerBar"></div></div>' +
      '<div class="loops-q" id="loopsQText"></div>' +
      '<div id="loopsOptsWrap" class="loops-opts"></div>' +
      '<div id="loopsTypedWrap" style="display:none;">' +
      '<input class="loops-input" id="loopsTypedInput" placeholder="Type your answer..." autocomplete="off" />' +
      '<button class="loops-btn" id="loopsSubmitBtn">Submit</button></div>' +
      '<div id="loopsReportWrap" style="text-align:center;"></div>' +
      '<div id="loopsFb" class="loops-fb" style="display:none;"></div>' +
      '<button class="loops-btn" id="loopsNextBtn" style="display:none;margin-top:10px;">Next →</button>' +
      "</div>" +
      '<div id="loopsResult" class="loops-screen"><div class="loops-result">' +
      '<div id="loopsResultTitle" style="font-size:1.2rem;font-weight:800;margin-bottom:8px;"></div>' +
      '<div class="big" id="loopsResultTime"></div>' +
      '<div style="opacity:.7;font-size:.85rem;margin-top:4px;" id="loopsResultScore"></div>' +
      '<div id="loopsResultBreakdown" class="loops-breakdown"></div>' +
      '<div class="loops-stack"><button class="loops-btn" id="loopsNextLevelBtn" style="display:none;">Next level →</button>' +
      '<button class="loops-btn" id="loopsAgainBtn">Play again</button>' +
      '<button class="loops-btn ghost" id="loopsBackBtn">Back to loops</button></div>' +
      "</div></div>" +
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

    el("loopsResetBtn").addEventListener("click", function () {
      if (!confirm("Reset all progress for this game?")) return;
      save = { unlocked: 0, best: {}, bestScore: {}, mastery: {} };
      persist();
      renderHome();
    });
  }

  // ── HOME ──
  function renderHome() {
    show("loopsHome");
    var grid = el("loopsGrid");
    grid.innerHTML = "";

    var ws = weakSpots();
    if (ws.length > 0) {
      var wsTile = document.createElement("div");
      wsTile.className = "loops-tile weak";
      wsTile.innerHTML =
        '<div class="loops-tile-top"><span>🎯</span><span>Weak Spots</span><span class="loops-badge">' + ws.length + '</span>' +
        '<button class="loops-ws-info" id="loopsWsInfoBtn" title="What is this?">ⓘ</button></div>' +
        '<div class="loops-tile-meta">You&#39;re closer than you think — ' + MASTERY_TARGET + ' correct and any question is yours for good.</div>' +
        '<div class="loops-tile-meta">Tap to level up →</div>';
      wsTile.addEventListener("click", function (e) {
        if (e.target && e.target.id === "loopsWsInfoBtn") {
          el("loopsWsOverlay").classList.add("open");
          return;
        }
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
        '<div class="loops-tile-top"><span>' + (loop.emoji || "🔹") + "</span><span>" + loop.name + "</span></div>" +
        '<div class="loops-tile-meta">' + loop.qs.length + " questions · Best time: " + (best ? fmtTime(best) : "—") + "</div>" +
        '<div class="loops-tile-meta">High score: ' + (bestScore !== undefined ? (bestScore + "/" + loop.qs.length) : "—") + "</div>" +
        '<div class="loops-tile-meta">' + (unlocked ? "Tap to play →" : "🔒 Locked") + "</div>";
      if (unlocked) tile.addEventListener("click", function () { openLoop(idx); });
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
    G.startMs = performance.now();
    show("loopsPlay");
    toneStart();
    renderQuestion();
  }

  function openReview(items, label) {
    G.mode = "review";
    G.reviewLabel = label;
    G.queue = shuffle(items.map(function (item) { return item.q; }));
    G.qi = 0; G.correct = 0; G.wrongs = 0; G.requeued = {}; G.seenKeys = {}; G.firstTryCorrect = 0; G.roundLog = [];
    G.startMs = performance.now();
    show("loopsPlay");
    toneStart();
    renderQuestion();
  }

  function renderQuestion() {
    var q = G.queue[G.qi];
    G.answered = false;
    G.lastUserAnswer = null;
    var timeLimit = G.mode === "loop" ? (GAME.loops[G.loopIdx].timeLimit || 15) : 15;
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
    G.t = limit;
    updateBar(limit, limit);
    el("loopsTimerLabel").textContent = limit.toFixed(0) + "s";
    G.timer = setInterval(function () {
      G.t -= 0.1;
      updateBar(G.t, limit);
      el("loopsTimerLabel").textContent = Math.max(0, G.t).toFixed(1) + "s";
      if (G.t <= 0) { clearInterval(G.timer); timeUp(); }
    }, 100);
  }
  function updateBar(t, limit) {
    var pct = Math.max(0, (t / limit) * 100);
    var bar = el("loopsTimerBar");
    bar.style.width = pct + "%";
    bar.style.background = pct < 25 ? "#c94c4c" : pct < 50 ? "#c9a84c" : "#00c2b3";
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
    } else {
      showFeedback(ok, q, ok ? pick(CORRECT_PHRASES) : (pick(WRONG_PHRASES) + " — " + q.a + ". You'll get it."));
    }
  }

  function showFeedback(ok, q, msg, mastered, isHtml) {
    var fb = el("loopsFb");
    fb.className = "loops-fb " + (mastered ? "mastered" : (ok ? "good" : "bad"));
    if (isHtml) { fb.innerHTML = msg; } else { fb.textContent = msg; }
    fb.style.display = "block";
    var nextBtn = el("loopsNextBtn");
    nextBtn.style.display = "block";
    nextBtn.onclick = nextQuestion;
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
    var html = '<div class="loops-bd-label">Here\'s how that round went — nice work getting through it 👇</div>';
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
        html += '<div class="loops-bd-detail">You said: ' + given + ' — <span class="loops-bd-pill">' + escapeHtml(row.correctAnswer) + '</span>. You\'ll get it next time.</div>';
      }
      html += '</div></div>';
    }
    wrap.innerHTML = html;
  }

  function finishRound() {
    clearInterval(G.timer);
    flushAnsweredStat();
    var elapsed = (performance.now() - G.startMs) / 1000;

    if (G.mode === "review") {
      renderBreakdown(G.roundLog);
      show("loopsResult");
      el("loopsNextLevelBtn").style.display = "none";
      el("loopsAgainBtn").className = "loops-btn";
      el("loopsResultTitle").textContent = "✓ Review complete — great effort";
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

    if (save.unlocked === G.loopIdx && G.loopIdx < GAME.loops.length - 1) {
      save.unlocked = G.loopIdx + 1; // finishing unlocks the next loop regardless of mistakes
    }
    persist();

    renderBreakdown(G.roundLog);
    show("loopsResult");
    el("loopsResultTitle").textContent = isNewBestTime ? "🏆 New best time! Brilliant." : "🎉 Loop complete — well done!";
    el("loopsResultTime").textContent = fmtTime(elapsed);
    el("loopsResultScore").textContent = "Score: " + G.firstTryCorrect + "/" + totalQs + (isNewBestScore ? " — new high score!" : "") +
      (G.wrongs === 0 ? " — clean run, nice." : "");
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

  // ── INIT ──
  window.LoopsEngine = {
    init: function (gameData) {
      try {
        GAME = gameData;
        if (!GAME || !GAME.loops || !GAME.loops.length) throw new Error("This game has no playable content.");
        loadSave();
        buildQuestionIndex();
        injectStyles();
        buildSkeleton();
        renderHome();
        pingPlayerSeenOnce();
      } catch (err) {
        var root = document.getElementById("loopsApp");
        if (root) {
          root.innerHTML =
            '<div style="max-width:420px;margin:40px auto;text-align:center;font-family:system-ui,sans-serif;padding:24px;">' +
            '<div style="font-size:2rem;margin-bottom:10px;">⚠️</div>' +
            '<div style="font-weight:800;font-size:1.1rem;margin-bottom:8px;">This game hit a snag loading</div>' +
            '<div style="opacity:.7;font-size:.9rem;">If you just got here from a fresh link, this can take a minute to go live \u2014 try refreshing. If it keeps happening, let whoever made this game know.</div>' +
            "</div>";
        }
        if (window.console) console.error("LoopsEngine failed to init:", err);
      }
    }
  };
})();
