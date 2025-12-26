(() => {
  "use strict";

  // ===== Config =====
  const N = 9;
  const EMPTY = 0, BLACK = 1, WHITE = 2;

  // Canvas render params will be computed responsively.
  const canvas = document.getElementById("board");
  const ctx = canvas.getContext("2d");

  // UI refs
  const newBtn = document.getElementById("newBtn");
  const undoBtn = document.getElementById("undoBtn");
  const passBtn = document.getElementById("passBtn");
  const resignBtn = document.getElementById("resignBtn");
  const levelSel = document.getElementById("levelSel");
  const hintSel = document.getElementById("hintSel");
  const komiInp = document.getElementById("komiInp");
  const turnTxt = document.getElementById("turnTxt");
  const msg = document.getElementById("msg");
  const capB = document.getElementById("capB");
  const capW = document.getElementById("capW");

  const scoringBox = document.getElementById("scoringBox");
  const calcBtn = document.getElementById("calcBtn");
  const exitScoreBtn = document.getElementById("exitScoreBtn");
  const scoreOut = document.getElementById("scoreOut");

  // ===== State =====
  let board = new Array(N * N).fill(EMPTY);
  let toPlay = BLACK;         // user is BLACK
  let gameOver = false;
  let inScoring = false;
  let lastMove = null;        // {x,y,color,pass}
  let consecutivePasses = 0;
  let captures = { [BLACK]: 0, [WHITE]: 0 };
  let history = [];           // for undo: snapshots
  let positionSet = new Set();// Superko: store hashes of positions (board + toPlay)
  let deadMask = new Array(N * N).fill(false); // scoring mode dead groups

  // Simple capture animation: record recently removed stones
  let flashCaptures = []; // array of {idx, t0}

  // Hover / hint
  let hover = { x: -1, y: -1, ok: false, reason: "" };
  let showHints = true;

  // ===== Helpers =====
  const idx = (x, y) => y * N + x;
  const inBounds = (x, y) => x >= 0 && x < N && y >= 0 && y < N;
  const other = (c) => (c === BLACK ? WHITE : BLACK);

  function cloneBoard(b) { return b.slice(); }
  function boardKey(b, nextPlayer) {
    // fast enough for 9x9
    return b.join("") + "|" + nextPlayer;
  }

  function neighbors(x, y) {
    const out = [];
    if (x > 0) out.push([x - 1, y]);
    if (x < N - 1) out.push([x + 1, y]);
    if (y > 0) out.push([x, y - 1]);
    if (y < N - 1) out.push([x, y + 1]);
    return out;
  }

  function floodGroup(b, sx, sy) {
    const color = b[idx(sx, sy)];
    const q = [[sx, sy]];
    const seen = new Set([idx(sx, sy)]);
    const stones = [];
    while (q.length) {
      const [x, y] = q.pop();
      stones.push([x, y]);
      for (const [nx, ny] of neighbors(x, y)) {
        const ni = idx(nx, ny);
        if (!seen.has(ni) && b[ni] === color) {
          seen.add(ni);
          q.push([nx, ny]);
        }
      }
    }
    return { color, stones };
  }

  function countLiberties(b, group) {
    const libs = new Set();
    for (const [x, y] of group.stones) {
      for (const [nx, ny] of neighbors(x, y)) {
        const ni = idx(nx, ny);
        if (b[ni] === EMPTY) libs.add(ni);
      }
    }
    return libs.size;
  }

  function removeGroup(b, group) {
    for (const [x, y] of group.stones) b[idx(x, y)] = EMPTY;
  }

  function applyMove(b, x, y, color) {
    // Returns { ok, b2, capturedCount, capturedIdxs, reason }
    const i = idx(x, y);
    if (b[i] !== EMPTY) return { ok: false, reason: "此點已有棋子" };

    const b2 = cloneBoard(b);
    b2[i] = color;

    // Capture opponent groups with 0 liberties after placement
    let captured = 0;
    const capturedIdxs = [];

    for (const [nx, ny] of neighbors(x, y)) {
      const ni = idx(nx, ny);
      if (b2[ni] === other(color)) {
        const g = floodGroup(b2, nx, ny);
        const libs = countLiberties(b2, g);
        if (libs === 0) {
          captured += g.stones.length;
          for (const [gx, gy] of g.stones) capturedIdxs.push(idx(gx, gy));
          removeGroup(b2, g);
        }
      }
    }

    // Suicide check (allowed only if capture happened and now has liberties)
    const myGroup = floodGroup(b2, x, y);
    const myLibs = countLiberties(b2, myGroup);
    if (myLibs === 0) {
      return { ok: false, reason: "自殺（無氣）禁著" };
    }

    return { ok: true, b2, capturedCount: captured, capturedIdxs, reason: "" };
  }

  function isLegalMove(b, x, y, color, posSet) {
    if (!inBounds(x, y)) return { ok: false, reason: "超出棋盤" };
    if (b[idx(x, y)] !== EMPTY) return { ok: false, reason: "已有棋子" };

    const res = applyMove(b, x, y, color);
    if (!res.ok) return res;

    // Superko: disallow repeating any previous position (positional superko + side to move)
    const key = boardKey(res.b2, other(color));
    if (posSet.has(key)) return { ok: false, reason: "重複局面（Superko）禁著" };

    return { ok: true, b2: res.b2, capturedCount: res.capturedCount, capturedIdxs: res.capturedIdxs };
  }

  function snapshotPush() {
    history.push({
      board: cloneBoard(board),
      toPlay,
      gameOver,
      inScoring,
      lastMove: lastMove ? { ...lastMove } : null,
      consecutivePasses,
      captures: { [BLACK]: captures[BLACK], [WHITE]: captures[WHITE] },
      positionSet: new Set(positionSet),
      deadMask: deadMask.slice(),
    });
    if (history.length > 200) history.shift();
  }

  function snapshotPop() {
    const s = history.pop();
    if (!s) return false;
    board = s.board;
    toPlay = s.toPlay;
    gameOver = s.gameOver;
    inScoring = s.inScoring;
    lastMove = s.lastMove;
    consecutivePasses = s.consecutivePasses;
    captures = s.captures;
    positionSet = s.positionSet;
    deadMask = s.deadMask;
    return true;
  }

  // ===== Atari detection (叫吃) =====
  function groupsWithLiberties(b, color) {
    const seen = new Set();
    const out = [];
    for (let y = 0; y < N; y++) {
      for (let x = 0; x < N; x++) {
        const i = idx(x, y);
        if (b[i] !== color || seen.has(i)) continue;
        const g = floodGroup(b, x, y);
        for (const [gx, gy] of g.stones) seen.add(idx(gx, gy));
        out.push({ group: g, libs: countLiberties(b, g) });
      }
    }
    return out;
  }

  function computeAtariInfo() {
    const blacks = groupsWithLiberties(board, BLACK).filter(g => g.libs === 1);
    const whites = groupsWithLiberties(board, WHITE).filter(g => g.libs === 1);
    return { blacks, whites };
  }

  // ===== Scoring (Japanese-style territory + prisoners + komi, with manual dead marking) =====
  function toggleDeadGroupAt(x, y) {
    const c = board[idx(x, y)];
    if (c === EMPTY) return;
    const g = floodGroup(board, x, y);
    // Determine current state: if any stone in group is dead -> treat as dead, else alive
    let anyDead = false;
    for (const [gx, gy] of g.stones) if (deadMask[idx(gx, gy)]) { anyDead = true; break; }
    const newVal = !anyDead;
    for (const [gx, gy] of g.stones) deadMask[idx(gx, gy)] = newVal;
  }

  function scoringBoardAndPrisoners() {
    // Start from current board; remove dead stones, count them as prisoners for opponent.
    const b2 = cloneBoard(board);
    let deadBlack = 0, deadWhite = 0;
    for (let i = 0; i < b2.length; i++) {
      if (!deadMask[i]) continue;
      if (b2[i] === BLACK) deadBlack++;
      if (b2[i] === WHITE) deadWhite++;
      b2[i] = EMPTY;
    }
    return {
      b2,
      extraPrisonersFor: {
        [BLACK]: deadWhite, // white dead -> black gets prisoners
        [WHITE]: deadBlack,
      }
    };
  }

  function territoryScore(b2) {
    // Flood fill empty regions, assign territory if bordered by single color.
    const seen = new Set();
    let terrB = 0, terrW = 0;
    let neutral = 0;

    for (let y = 0; y < N; y++) {
      for (let x = 0; x < N; x++) {
        const start = idx(x, y);
        if (b2[start] !== EMPTY || seen.has(start)) continue;

        const q = [[x, y]];
        seen.add(start);
        const empties = [];
        const borders = new Set();

        while (q.length) {
          const [cx, cy] = q.pop();
          empties.push([cx, cy]);
          for (const [nx, ny] of neighbors(cx, cy)) {
            const ni = idx(nx, ny);
            const v = b2[ni];
            if (v === EMPTY && !seen.has(ni)) {
              seen.add(ni);
              q.push([nx, ny]);
            } else if (v === BLACK || v === WHITE) {
              borders.add(v);
            }
          }
        }

        if (borders.size === 1) {
          const only = [...borders][0];
          if (only === BLACK) terrB += empties.length;
          else terrW += empties.length;
        } else {
          neutral += empties.length;
        }
      }
    }
    return { terrB, terrW, neutral };
  }

  function calcFinalScore() {
    const komi = Number(komiInp.value || "6.5");
    const { b2, extraPrisonersFor } = scoringBoardAndPrisoners();
    const terr = territoryScore(b2);

    const prisonersB = captures[BLACK] + extraPrisonersFor[BLACK];
    const prisonersW = captures[WHITE] + extraPrisonersFor[WHITE];

    // Japanese-ish: score = territory + prisoners, white adds komi
    const scoreB = terr.terrB + prisonersB;
    const scoreW = terr.terrW + prisonersW + komi;

    let winner = "平手";
    if (scoreB > scoreW) winner = `黑勝 ${ (scoreB - scoreW).toFixed(1) }`;
    else if (scoreW > scoreB) winner = `白勝 ${ (scoreW - scoreB).toFixed(1) }`;

    return {
      komi,
      ...terr,
      prisonersB,
      prisonersW,
      scoreB,
      scoreW,
      winner,
    };
  }

  // ===== AI =====
  function legalMovesList(b, color, posSet) {
    const moves = [];
    for (let y = 0; y < N; y++) for (let x = 0; x < N; x++) {
      const res = isLegalMove(b, x, y, color, posSet);
      if (res.ok) moves.push({ x, y });
    }
    // PASS is always legal (we allow)
    moves.push({ pass: true });
    return moves;
  }

  function heuristicEvaluateMove(b, color, move, posSet) {
    if (move.pass) return -0.5; // slight discourage pass
    const res = isLegalMove(b, move.x, move.y, color, posSet);
    if (!res.ok) return -1e9;

    const b2 = res.b2;

    // features
    let score = 0;

    // capture reward
    score += res.capturedCount * 4.0;

    // center preference
    const cx = (N - 1) / 2, cy = (N - 1) / 2;
    const dx = move.x - cx, dy = move.y - cy;
    score += 1.2 * (1.0 - (Math.abs(dx) + Math.abs(dy)) / (N - 1));

    // avoid self-atari
    const g = floodGroup(b2, move.x, move.y);
    const libs = countLiberties(b2, g);
    if (libs === 1) score -= 3.5;
    if (libs === 2) score -= 0.6;

    // put opponent in atari
    const opp = other(color);
    for (const [nx, ny] of neighbors(move.x, move.y)) {
      if (b2[idx(nx, ny)] === opp) {
        const og = floodGroup(b2, nx, ny);
        const ol = countLiberties(b2, og);
        if (ol === 1) score += 2.0;
      }
    }

    // prefer connecting to own stones a bit
    let adjOwn = 0;
    for (const [nx, ny] of neighbors(move.x, move.y)) if (b[idx(nx, ny)] === color) adjOwn++;
    score += adjOwn * 0.35;

    return score;
  }

  function randomPlayout(b, color, posSet, maxSteps = 22) {
    // very lightweight playout: choose random legal (excluding too many passes)
    let b2 = cloneBoard(b);
    let c = color;
    let passes = 0;

    // local superko set for playout
    const localSet = new Set(posSet);

    for (let step = 0; step < maxSteps; step++) {
      const moves = legalMovesList(b2, c, localSet);
      // reduce pass likelihood
      const nonPass = moves.filter(m => !m.pass);
      const chosen = (nonPass.length && Math.random() < 0.92)? 
        nonPass[Math.floor(Math.random() * nonPass.length)]
        : { pass: true };

      if (chosen.pass) {
        passes++;
        if (passes >= 2) break;
        c = other(c);
        continue;
      }

      const res = isLegalMove(b2, chosen.x, chosen.y, c, localSet);
      if (!res.ok) { c = other(c); continue; }

      b2 = res.b2;
      localSet.add(boardKey(b2, other(c)));
      passes = 0;
      c = other(c);
    }

    // Simple outcome estimate: (stones + territory) difference (rough)
    const approx = approximateAreaDiff(b2);
    return approx; // positive favors black, negative favors white
  }

  function approximateAreaDiff(b2) {
    // quick and dirty: stones on board + territory estimate via region border
    let blackStones = 0, whiteStones = 0;
    for (const v of b2) { if (v === BLACK) blackStones++; else if (v === WHITE) whiteStones++; }
    const terr = territoryScore(b2);
    return (blackStones + terr.terrB) - (whiteStones + terr.terrW);
  }

  function chooseAIMove() {
    const color = WHITE;

    const moves = legalMovesList(board, color, positionSet);
    // If only pass, pass
    if (moves.length === 1) return moves[0];

    if (levelSel.value === "basic") {
      let best = null, bestScore = -1e18;
      for (const m of moves) {
        const s = heuristicEvaluateMove(board, color, m, positionSet);
        if (s > bestScore) { bestScore = s; best = m; }
      }
      return best || { pass: true };
    }

    // Advanced: heuristic + small Monte Carlo rollouts
    let candidates = moves
      .filter(m => !m.pass)
      .map(m => ({ m, h: heuristicEvaluateMove(board, color, m, positionSet) }))
      .sort((a, b) => b.h - a.h)
      .slice(0, 10); // top-k

    if (!candidates.length) return { pass: true };

    const simsPerMove = 50; // keep light
    let best = candidates[0].m;
    let bestVal = -1e18;

    for (const { m, h } of candidates) {
      const res = isLegalMove(board, m.x, m.y, color, positionSet);
      if (!res.ok) continue;

      // start from after move
      const bAfter = res.b2;
      const localSet = new Set(positionSet);
      localSet.add(boardKey(bAfter, BLACK));

      let sum = 0;
      for (let k = 0; k < simsPerMove; k++) {
        const diff = randomPlayout(bAfter, BLACK, localSet, 18);
        // AI is WHITE => wants diff (black-white) as small as possible
        sum += (-diff);
      }
      const mc = sum / simsPerMove;

      // blend
      const val = mc + h * 0.35;
      if (val > bestVal) { bestVal = val; best = m; }
    }

    return best;
  }

  // ===== Game flow =====
  function setMessage(text) { msg.textContent = text; }

  function updateUI() {
    capB.textContent = String(captures[BLACK]);
    capW.textContent = String(captures[WHITE]);

    if (gameOver) {
      turnTxt.textContent = "對局結束";
      return;
    }
    if (toPlay === BLACK) turnTxt.textContent = "輪到：黑（你）";
    else turnTxt.textContent = "輪到：白（電腦思考中…）";
  }

  function endGame(reason) {
    gameOver = true;
    inScoring = true;
    scoringBox.style.display = "block";
    setMessage(`終局：${reason}。已進入終局決算模式（可標記死活後計分）。`);
    updateUI();
    render();
  }

  function startNewGame() {
    board = new Array(N * N).fill(EMPTY);
    toPlay = BLACK;
    gameOver = false;
    inScoring = false;
    lastMove = null;
    consecutivePasses = 0;
    captures = { [BLACK]: 0, [WHITE]: 0 };
    history = [];
    positionSet = new Set();
    deadMask = new Array(N * N).fill(false);
    flashCaptures = [];
    scoreOut.textContent = "";
    scoringBox.style.display = "none";
    setMessage("新局開始：你先手黑棋。");
    positionSet.add(boardKey(board, toPlay));
    updateUI();
    render();
  }

  function doPass() {
    if (gameOver) return;
    if (toPlay !== BLACK) return;

    snapshotPush();

    lastMove = { pass: true, color: BLACK };
    consecutivePasses++;

    // update superko key for next player with same board
    toPlay = WHITE;
    positionSet.add(boardKey(board, toPlay));

    if (consecutivePasses >= 2) {
      endGame("雙方連續 PASS");
      return;
    }
    setMessage("你 PASS。電腦回合。");
    updateUI();
    render();
    setTimeout(aiTurn, 160);
  }

  function doResign() {
    if (gameOver) return;
    endGame("黑棋投降（白勝）");
  }

  function doUndo() {
    if (!history.length) { setMessage("沒有可悔棋的步數。"); return; }
    snapshotPop();
    // If undo lands on AI turn, undo once more to give player turn back (optional)
    if (!gameOver && toPlay === WHITE && history.length) snapshotPop();
    setMessage("已悔棋。");
    updateUI();
    render();
  }

  function playAt(x, y) {
    if (gameOver) return;
    if (toPlay !== BLACK) return;

    // In scoring mode: toggle dead group
    if (inScoring) {
      if (board[idx(x, y)] !== EMPTY) {
        toggleDeadGroupAt(x, y);
        setMessage("已切換該團死活狀態（半透明=死棋）。");
        render();
      }
      return;
    }

    const legal = isLegalMove(board, x, y, BLACK, positionSet);
    if (!legal.ok) {
      setMessage(`禁著：${legal.reason}`);
      render();
      return;
    }

    snapshotPush();

    // apply
    board = legal.b2;
    captures[BLACK] += legal.capturedCount;
    if (legal.capturedIdxs.length) {
      const t0 = performance.now();
      for (const i of legal.capturedIdxs) flashCaptures.push({ idx: i, t0 });
    }

    lastMove = { x, y, color: BLACK };
    consecutivePasses = 0;

    // update turn + superko
    toPlay = WHITE;
    positionSet.add(boardKey(board, toPlay));

    // post move messages: atari warning
    const at = computeAtariInfo();
    const warnW = at.whites.length ? "（白棋有叫吃）" : "";
    const warnB = at.blacks.length ? "（黑棋有叫吃）" : "";
    setMessage(`你落子：(${x + 1},${y + 1})。${warnW}${warnB}`);
    updateUI();
    render();

    setTimeout(aiTurn, 180);
  }

  function aiTurn() {
    if (gameOver) return;
    if (toPlay !== WHITE) return;
    if (inScoring) return;

    const move = chooseAIMove();

    snapshotPush();

    if (move.pass) {
      lastMove = { pass: true, color: WHITE };
      consecutivePasses++;
      toPlay = BLACK;
      positionSet.add(boardKey(board, toPlay));

      if (consecutivePasses >= 2) {
        endGame("雙方連續 PASS");
        return;
      }
      setMessage("電腦 PASS。輪到你。");
      updateUI();
      render();
      return;
    }

    const legal = isLegalMove(board, move.x, move.y, WHITE, positionSet);
    if (!legal.ok) {
      // fallback: pass
      lastMove = { pass: true, color: WHITE };
      consecutivePasses++;
      toPlay = BLACK;
      positionSet.add(boardKey(board, toPlay));
      setMessage("電腦找不到合適落子（改 PASS）。輪到你。");
      updateUI();
      render();
      return;
    }

    board = legal.b2;
    captures[WHITE] += legal.capturedCount;
    if (legal.capturedIdxs.length) {
      const t0 = performance.now();
      for (const i of legal.capturedIdxs) flashCaptures.push({ idx: i, t0 });
    }

    lastMove = { x: move.x, y: move.y, color: WHITE };
    consecutivePasses = 0;

    toPlay = BLACK;
    positionSet.add(boardKey(board, toPlay));

    const at = computeAtariInfo();
    const warnW = at.whites.length ? "（白棋有叫吃）" : "";
    const warnB = at.blacks.length ? "（黑棋有叫吃）" : "";
    setMessage(`電腦落子：(${move.x + 1},${move.y + 1})。${warnW}${warnB} 輪到你。`);
    updateUI();
    render();
  }

  // ===== Rendering =====
  function resizeCanvasForDPR() {
    const dpr = window.devicePixelRatio || 1;
    const rect = canvas.getBoundingClientRect();
    const w = Math.round(rect.width * dpr);
    const h = Math.round(rect.height * dpr);
    if (canvas.width !== w || canvas.height !== h) {
      canvas.width = w;
      canvas.height = h;
    }
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0); // draw in CSS pixels
  }

  function drawBoard() {
    resizeCanvasForDPR();

    const rect = canvas.getBoundingClientRect();
    const W = rect.width, H = rect.height;

    // layout
    const pad = Math.max(26, Math.min(W, H) * 0.06);
    const size = Math.min(W, H) - pad * 2;
    const step = size / (N - 1);
    const originX = (W - size) / 2;
    const originY = (H - size) / 2;

    // background already via CSS; draw grid + star points
    ctx.clearRect(0, 0, W, H);

    // subtle vignette
    const g = ctx.createRadialGradient(W*0.35, H*0.25, 20, W*0.5, H*0.5, Math.max(W,H)*0.8);
    g.addColorStop(0, "rgba(255,255,255,0.08)");
    g.addColorStop(1, "rgba(0,0,0,0.10)");
    ctx.fillStyle = g;
    ctx.fillRect(0, 0, W, H);

    // grid
    ctx.lineWidth = 2;
    ctx.strokeStyle = "rgba(0,0,0,0.65)";
    ctx.beginPath();
    for (let i = 0; i < N; i++) {
      const x = originX + i * step;
      const y = originY + i * step;
      ctx.moveTo(originX, y);
      ctx.lineTo(originX + size, y);
      ctx.moveTo(x, originY);
      ctx.lineTo(x, originY + size);
    }
    ctx.stroke();

    // star points for 9x9: (2,2)(2,6)(6,2)(6,6)(4,4) in 0-based
    const hoshi = [[2,2],[2,6],[6,2],[6,6],[4,4]];
    ctx.fillStyle = "rgba(0,0,0,0.75)";
    for (const [hx, hy] of hoshi) {
      ctx.beginPath();
      ctx.arc(originX + hx*step, originY + hy*step, 4.2, 0, Math.PI*2);
      ctx.fill();
    }

    // compute atari groups for outlines
    const at = computeAtariInfo();
    const atariSet = new Set();
    for (const g of at.blacks) for (const [x,y] of g.group.stones) atariSet.add(idx(x,y));
    for (const g of at.whites) for (const [x,y] of g.group.stones) atariSet.add(idx(x,y));

    // stones
    const r = step * 0.43;
    for (let y = 0; y < N; y++) for (let x = 0; x < N; x++) {
      const v = board[idx(x,y)];
      if (v === EMPTY) continue;

      const cx = originX + x*step;
      const cy = originY + y*step;

      const isDead = inScoring && deadMask[idx(x,y)];
      const alpha = isDead ? 0.35 : 1.0;

      // shadow
      ctx.save();
      ctx.globalAlpha = alpha;
      ctx.beginPath();
      ctx.fillStyle = "rgba(0,0,0,0.30)";
      ctx.arc(cx + 2.2, cy + 2.8, r, 0, Math.PI*2);
      ctx.fill();

      // stone body
      ctx.beginPath();
      const stoneGrad = ctx.createRadialGradient(cx - r*0.35, cy - r*0.35, r*0.2, cx, cy, r*1.2);
      if (v === BLACK) {
        stoneGrad.addColorStop(0, "rgba(80,80,90,1)");
        stoneGrad.addColorStop(1, "rgba(10,10,14,1)");
      } else {
        stoneGrad.addColorStop(0, "rgba(255,255,255,1)");
        stoneGrad.addColorStop(1, "rgba(210,215,225,1)");
      }
      ctx.fillStyle = stoneGrad;
      ctx.arc(cx, cy, r, 0, Math.PI*2);
      ctx.fill();

      // outline
      ctx.lineWidth = 1.8;
      ctx.strokeStyle = v === BLACK ? "rgba(255,255,255,0.18)" : "rgba(0,0,0,0.22)";
      ctx.stroke();

      // atari warning outline
      if (!inScoring && atariSet.has(idx(x,y))) {
        ctx.lineWidth = 3.2;
        ctx.strokeStyle = "rgba(255, 215, 80, 0.85)";
        ctx.stroke();
      }

      ctx.restore();
    }

    // last move marker
    if (lastMove && !lastMove.pass && lastMove.x != null) {
      const cx = originX + lastMove.x*step;
      const cy = originY + lastMove.y*step;
      ctx.beginPath();
      ctx.lineWidth = 3;
      ctx.strokeStyle = "rgba(125,211,252,0.90)";
      ctx.arc(cx, cy, r*0.45, 0, Math.PI*2);
      ctx.stroke();
    }

    // capture flash markers
    const now = performance.now();
    flashCaptures = flashCaptures.filter(o => now - o.t0 < 320);
    if (flashCaptures.length) {
      for (const o of flashCaptures) {
        const x = o.idx % N;
        const y = Math.floor(o.idx / N);
        const cx = originX + x*step;
        const cy = originY + y*step;
        const t = (now - o.t0) / 320;
        ctx.save();
        ctx.globalAlpha = (1 - t) * 0.55;
        ctx.beginPath();
        ctx.fillStyle = "rgba(255,255,255,0.95)";
        ctx.arc(cx, cy, r*0.55 + t*r*0.9, 0, Math.PI*2);
        ctx.fill();
        ctx.restore();
      }
      requestAnimationFrame(render);
    }

    // hover preview / legal hints
    if (!gameOver && !inScoring && toPlay === BLACK) {
      if (hover.x >= 0) {
        const cx = originX + hover.x*step;
        const cy = originY + hover.y*step;
        ctx.save();
        ctx.globalAlpha = 0.65;
        ctx.beginPath();
        ctx.fillStyle = hover.ok ? "rgba(0,0,0,0.45)" : "rgba(255, 80, 80, 0.35)";
        ctx.arc(cx, cy, r*0.70, 0, Math.PI*2);
        ctx.fill();
        ctx.restore();
      }

      if (showHints) {
        // draw small dots on legal moves, small X on illegal (optional heavy)
        // keep it light: only show nearby? We'll show all legal dots for 9x9 (81 max).
        const dots = [];
        for (let y = 0; y < N; y++) for (let x = 0; x < N; x++) {
          if (board[idx(x,y)] !== EMPTY) continue;
          const ok = isLegalMove(board, x, y, BLACK, positionSet).ok;
          dots.push({ x, y, ok });
        }
        for (const d of dots) {
          const px = originX + d.x*step;
          const py = originY + d.y*step;
          ctx.save();
          ctx.globalAlpha = d.ok ? 0.42 : 0.25;
          ctx.fillStyle = d.ok ? "rgba(0,0,0,0.85)" : "rgba(120,0,0,0.85)";
          ctx.beginPath();
          ctx.arc(px, py, d.ok ? 3.0 : 2.2, 0, Math.PI*2);
          ctx.fill();
          ctx.restore();
        }
      }
    }

    // Store mapping for hit test
    drawBoard._geom = { originX, originY, size, step, pad };
  }

  function render() { drawBoard(); }

  function hitTest(clientX, clientY) {
    const rect = canvas.getBoundingClientRect();
    const x = clientX - rect.left;
    const y = clientY - rect.top;
    const g = drawBoard._geom;
    if (!g) return null;

    const { originX, originY, step } = g;

    const fx = (x - originX) / step;
    const fy = (y - originY) / step;
    const ix = Math.round(fx);
    const iy = Math.round(fy);
    if (!inBounds(ix, iy)) return null;

    // threshold
    const px = originX + ix * step;
    const py = originY + iy * step;
    const dist = Math.hypot(px - x, py - y);
    if (dist > step * 0.55) return null;

    return { x: ix, y: iy };
  }

  // ===== Events =====
  canvas.addEventListener("mousemove", (e) => {
    const p = hitTest(e.clientX, e.clientY);
    if (!p || gameOver || inScoring || toPlay !== BLACK) {
      hover = { x: -1, y: -1, ok: false, reason: "" };
      render();
      return;
    }
    const legal = isLegalMove(board, p.x, p.y, BLACK, positionSet);
    hover = { x: p.x, y: p.y, ok: !!legal.ok, reason: legal.ok ? "" : legal.reason };
    render();
  });

  canvas.addEventListener("mouseleave", () => {
    hover = { x: -1, y: -1, ok: false, reason: "" };
    render();
  });

  canvas.addEventListener("click", (e) => {
    const p = hitTest(e.clientX, e.clientY);
    if (!p) return;
    playAt(p.x, p.y);
  });

  newBtn.addEventListener("click", startNewGame);
  passBtn.addEventListener("click", doPass);
  resignBtn.addEventListener("click", doResign);
  undoBtn.addEventListener("click", doUndo);

  hintSel.addEventListener("change", () => {
    showHints = hintSel.value === "on";
    render();
  });

  calcBtn.addEventListener("click", () => {
    const s = calcFinalScore();
    scoreOut.textContent =
      `Komi: ${s.komi}\n` +
      `黑領地: ${s.terrB}\n白領地: ${s.terrW}\n` +
      `中立空: ${s.neutral}\n\n` +
      `黑俘虜(提子+死棋): ${s.prisonersB}\n` +
      `白俘虜(提子+死棋): ${s.prisonersW}\n\n` +
      `黑總分: ${s.scoreB.toFixed(1)}\n` +
      `白總分: ${s.scoreW.toFixed(1)}\n\n` +
      `結果: ${s.winner}\n` +
      `\n（提示）若你覺得結果不合理，通常是死活標記還沒標完。`;
    setMessage("已計算分數。你可以繼續標記死活再重算。");
  });

  exitScoreBtn.addEventListener("click", () => {
    // allow returning to play (some teachers like it); but keep gameOver true if ended
    // We'll just exit scoring mode without changing gameOver. If gameOver, this is just browsing.
    inScoring = false;
    scoringBox.style.display = "none";
    setMessage(gameOver ? "對局已結束。" : "已回到對局。");
    render();
  });

  // Keyboard shortcuts (optional)
  window.addEventListener("keydown", (e) => {
    if (e.key === "p" || e.key === "P") doPass();
    if (e.key === "u" || e.key === "U") doUndo();
    if (e.key === "n" || e.key === "N") startNewGame();
  });

  window.addEventListener("resize", () => render());

  // ===== Init =====
  startNewGame();

  // Expose a quick way to enter scoring mode for demo:
  // You can force scoring mode by typing in console: __enterScore()
  window.__enterScore = () => {
    if (!gameOver) {
      inScoring = true;
      scoringBox.style.display = "block";
      setMessage("已手動進入終局決算模式。");
      render();
    }
  };

})();
