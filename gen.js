/* ENDLESS PUZZLE — 問題を作る心臓部（スリザーリンク・マインスイーパー）
 * ページ（ヒント用）とWorker（問題づくり）の両方で読み込む。
 * スリザーリンク：輪を作る→数字を全部置く→「論理だけで解ける」かつ「答えが1つ」の間だけ数字を消す。
 *   難しさ＝解くのに要る推理の深さ（1：数字と点の基本 2：短い仮定 3：長い仮定）。
 * マインスイーパー：最初に開いた場所から、当てずっぽうなしで最後まで解ける盤面だけを出す。
 */
(function (root) {
  'use strict';

  function rnd(n) { return Math.floor(Math.random() * n); }
  function shuffle(a) { for (let i = a.length - 1; i > 0; i--) { const j = rnd(i + 1); const t = a[i]; a[i] = a[j]; a[j] = t; } return a; }

  /* ================= スリザーリンク ================= */
  const geoCache = {};
  function geo(W, H) {
    const key = W + 'x' + H;
    if (geoCache[key]) return geoCache[key];
    const C = W * H, V = (W + 1) * (H + 1), NH = W * (H + 1), E = NH + (W + 1) * H;
    const hE = (x, y) => y * W + x, vE = (x, y) => NH + y * (W + 1) + x, vid = (x, y) => y * (W + 1) + x;
    const cellEdges = new Int32Array(C * 4);
    const edgeVerts = new Int32Array(E * 2);
    const edgeCells = []; for (let e = 0; e < E; e++) edgeCells.push([]);
    const vertEdges = []; for (let v = 0; v < V; v++) vertEdges.push([]);
    for (let y = 0; y <= H; y++) for (let x = 0; x < W; x++) { const e = hE(x, y); edgeVerts[2 * e] = vid(x, y); edgeVerts[2 * e + 1] = vid(x + 1, y); }
    for (let y = 0; y < H; y++) for (let x = 0; x <= W; x++) { const e = vE(x, y); edgeVerts[2 * e] = vid(x, y); edgeVerts[2 * e + 1] = vid(x, y + 1); }
    for (let e = 0; e < E; e++) { vertEdges[edgeVerts[2 * e]].push(e); vertEdges[edgeVerts[2 * e + 1]].push(e); }
    for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) {
      const c = y * W + x; const es = [hE(x, y), hE(x, y + 1), vE(x, y), vE(x + 1, y)];
      for (let k = 0; k < 4; k++) { cellEdges[4 * c + k] = es[k]; edgeCells[es[k]].push(c); }
    }
    const g = { W, H, C, V, E, NH, hE, vE, vid, cellEdges, edgeVerts, edgeCells, vertEdges };
    geoCache[key] = g;
    return g;
  }

  function newState(g) {
    const par = new Int32Array(g.V); for (let i = 0; i < g.V; i++) par[i] = i;
    return { e: new Int8Array(g.E), cl: new Int8Array(g.C), cx: new Int8Array(g.C), vl: new Int8Array(g.V), vx: new Int8Array(g.V), par, ce: new Int32Array(g.V), lines: 0, unk: g.E, done: false, bad: false };
  }
  function cloneState(s) {
    return { e: s.e.slice(), cl: s.cl.slice(), cx: s.cx.slice(), vl: s.vl.slice(), vx: s.vx.slice(), par: s.par.slice(), ce: s.ce.slice(), lines: s.lines, unk: s.unk, done: s.done, bad: false };
  }
  function find(p, x) { while (p[x] !== x) { p[x] = p[p[x]]; x = p[x]; } return x; }

  // 戻り値 true=置けた false=矛盾（s.bad）か手数切れ（ctx.out）
  function setE(ctx, s, e, val) {
    const cur = s.e[e];
    if (cur === val) return true;
    if (cur !== 0) { s.bad = true; return false; }
    if (s.done && val > 0) { s.bad = true; return false; }
    if (ctx.budget !== undefined) { if (ctx.budget <= 0) { ctx.out = true; return false; } ctx.budget--; }
    const g = ctx.g;
    s.e[e] = val; s.unk--;
    if (ctx.log) ctx.log.push(val > 0 ? e : ~e);
    const cs = g.edgeCells[e];
    const a = g.edgeVerts[2 * e], b = g.edgeVerts[2 * e + 1];
    if (val > 0) {
      for (let i = 0; i < cs.length; i++) s.cl[cs[i]]++;
      s.vl[a]++; s.vl[b]++; s.lines++;
      const ra = find(s.par, a), rb = find(s.par, b);
      if (ra === rb) {
        s.ce[ra]++;
        if (s.ce[ra] !== s.lines) { s.bad = true; return false; }
        const clues = ctx.clues;
        for (let c = 0; c < g.C; c++) { const k = clues[c]; if (k >= 0 && s.cl[c] !== k) { s.bad = true; return false; } }
        for (let v = 0; v < g.V; v++) { const d = s.vl[v]; if (d !== 0 && d !== 2) { s.bad = true; return false; } }
        s.done = true;
      } else { s.par[ra] = rb; s.ce[rb] += s.ce[ra] + 1; }
    } else {
      for (let i = 0; i < cs.length; i++) s.cx[cs[i]]++;
      s.vx[a]++; s.vx[b]++;
    }
    for (let i = 0; i < cs.length; i++) ctx.qc.push(cs[i]);
    ctx.qv.push(a, b);
    return true;
  }

  function closeWouldComplete(ctx, s, e) {
    const g = ctx.g, a = g.edgeVerts[2 * e];
    const r = find(s.par, a);
    if (s.ce[r] !== s.lines) return false;
    const clues = ctx.clues, cs = g.edgeCells[e];
    for (let c = 0; c < g.C; c++) {
      const k = clues[c]; if (k < 0) continue;
      const add = (cs[0] === c || cs[1] === c) ? 1 : 0;
      if (s.cl[c] + add !== k) return false;
    }
    return true;
  }

  function finishDone(ctx, s) {
    const g = ctx.g;
    for (let e = 0; e < g.E; e++) if (s.e[e] === 0) { s.e[e] = -1; s.unk--; if (ctx.log) ctx.log.push(~e); }
    ctx.qc.length = 0; ctx.qv.length = 0;
  }

  // 1=ok 0=矛盾 2=手数切れ
  function propagate(ctx, s) {
    const g = ctx.g, clues = ctx.clues;
    for (;;) {
      while (ctx.qc.length || ctx.qv.length) {
        if (s.done) { finishDone(ctx, s); return 1; }
        if (ctx.qc.length) {
          const c = ctx.qc.pop(); const k = clues[c]; if (k < 0) continue;
          const L = s.cl[c], X = s.cx[c], U = 4 - L - X;
          if (L > k || L + U < k) { s.bad = true; return 0; }
          if (U > 0 && (L === k || L + U === k)) {
            const val = L === k ? -1 : 1;
            for (let i = 0; i < 4; i++) { const e = g.cellEdges[4 * c + i]; if (s.e[e] === 0 && !setE(ctx, s, e, val)) return s.bad ? 0 : 2; }
          }
        } else {
          const v = ctx.qv.pop(); const es = g.vertEdges[v];
          const L = s.vl[v], X = s.vx[v], U = es.length - L - X;
          if (L > 2 || (L === 1 && U === 0)) { s.bad = true; return 0; }
          let val = 0;
          if (U > 0) { if (L === 2) val = -1; else if (L === 1 && U === 1) val = 1; else if (L === 0 && U === 1) val = -1; }
          if (val) for (let i = 0; i < es.length; i++) { const e = es[i]; if (s.e[e] === 0 && !setE(ctx, s, e, val)) return s.bad ? 0 : 2; }
        }
      }
      if (s.done) { finishDone(ctx, s); return 1; }
      // 早すぎる輪を作る線は×
      let changed = false;
      for (let e = 0; e < g.E; e++) {
        if (s.e[e] !== 0) continue;
        const a = g.edgeVerts[2 * e], b = g.edgeVerts[2 * e + 1];
        if (s.vl[a] !== 1 || s.vl[b] !== 1) continue;
        if (find(s.par, a) !== find(s.par, b)) continue;
        if (closeWouldComplete(ctx, s, e)) continue;
        if (!setE(ctx, s, e, -1)) return s.bad ? 0 : 2;
        changed = true;
      }
      if (!changed) return 1;
    }
  }

  function seedQueue(ctx) {
    const g = ctx.g;
    for (let c = 0; c < g.C; c++) if (ctx.clues[c] >= 0) ctx.qc.push(c);
    for (let v = 0; v < g.V; v++) ctx.qv.push(v);
  }

  const L2LIM = 6; // 「短い仮定」で許す手数

  // 仮定してみて矛盾したら逆に決める。1回でも決まったら true
  function trialPass(g, clues, s, lim, ctxMain) {
    let progress = false;
    for (let e = 0; e < g.E; e++) {
      if (s.e[e] !== 0) continue;
      for (let t = 0; t < 2; t++) {
        const val = t === 0 ? 1 : -1;
        const ts = cloneState(s);
        const tctx = { g, clues, qc: [], qv: [], budget: lim };
        let contra = false;
        if (!setE(tctx, ts, e, val)) contra = ts.bad;
        else contra = propagate(tctx, ts) === 0;
        if (contra) {
          if (!setE(ctxMain, s, e, -val)) return -1;
          if (propagate(ctxMain, s) === 0) return -1;
          progress = true;
          break;
        }
      }
      if (s.done) return 1;
    }
    return progress ? 1 : 0;
  }

  // level: 1/2/3。戻り値 {solved, usedClose, level(実際に要った深さ), state}
  function logicSolve(g, clues, level, init, log) {
    const ctx = { g, clues, qc: [], qv: [], log };
    const s = init ? cloneState(init) : newState(g);
    seedQueue(ctx);
    if (propagate(ctx, s) === 0) return { solved: false, contra: true, state: s };
    let used = 1;
    while (!s.done && level >= 2) {
      let r = trialPass(g, clues, s, L2LIM, ctx);
      if (r < 0) return { solved: false, contra: true, state: s };
      if (r > 0) { used = Math.max(used, 2); continue; }
      if (level < 3) break;
      r = trialPass(g, clues, s, Infinity, ctx);
      if (r < 0) return { solved: false, contra: true, state: s };
      if (r > 0) { used = 3; continue; }
      break;
    }
    if (s.done) return { solved: true, usedClose: false, level: used, state: s };
    // 残りが「閉じれば完成」の1本だけなら完成とみなす（答えが1つかは別に数える）
    for (let e = 0; e < g.E; e++) {
      if (s.e[e] !== 0) continue;
      const a = g.edgeVerts[2 * e], b = g.edgeVerts[2 * e + 1];
      if (s.vl[a] === 1 && s.vl[b] === 1 && find(s.par, a) === find(s.par, b) && closeWouldComplete(ctx, s, e)) {
        const t = cloneState(s); const c2 = { g, clues, qc: [], qv: [] };
        if (setE(c2, t, e, 1) && propagate(c2, t) !== 0 && t.done) return { solved: true, usedClose: true, level: used, state: t };
      }
    }
    return { solved: false, state: s };
  }

  function pickBranch(g, s) {
    let fallback = -1;
    for (let e = 0; e < g.E; e++) {
      if (s.e[e] !== 0) continue;
      const a = g.edgeVerts[2 * e], b = g.edgeVerts[2 * e + 1];
      if (s.vl[a] === 1 || s.vl[b] === 1) return e;
      if (fallback < 0) fallback = e;
    }
    return fallback;
  }

  // 答えの数を数える（limitで打ち切り）。手数が尽きたら -1
  function countSolutions(g, clues, limit, nodeLimit, collect) {
    limit = limit || 2; nodeLimit = nodeLimit || 4000;
    let count = 0, nodes = 0, over = false;
    const ctx = { g, clues, qc: [], qv: [] };
    const s0 = newState(g); seedQueue(ctx);
    if (propagate(ctx, s0) === 0) return 0;
    (function rec(s) {
      if (count >= limit || over) return;
      if (++nodes > nodeLimit) { over = true; return; }
      if (s.done) { count++; if (collect) collect.push(s.e.slice()); return; }
      const e = pickBranch(g, s); if (e < 0) return;
      for (let t = 0; t < 2; t++) {
        const ts = cloneState(s); const c = { g, clues, qc: [], qv: [] };
        if (setE(c, ts, e, t === 0 ? 1 : -1) && propagate(c, ts) !== 0) rec(ts);
        if (count >= limit || over) return;
      }
    })(s0);
    return over ? -1 : count;
  }

  // 穴のない領域を育てて、その縁を輪にする
  function makeRegion(W, H) {
    const N = W * H;
    const nb = (c) => { const x = c % W, y = (c / W) | 0, r = []; if (x > 0) r.push(c - 1); if (x < W - 1) r.push(c + 1); if (y > 0) r.push(c - W); if (y < H - 1) r.push(c + W); return r; };
    const at = (R, x, y) => (x < 0 || y < 0 || x >= W || y >= H) ? 0 : R[y * W + x];
    function diagOK(R, c) {
      const x = c % W, y = (c / W) | 0;
      for (let dy = -1; dy <= 0; dy++) for (let dx = -1; dx <= 0; dx++) {
        const x0 = x + dx, y0 = y + dy;
        if (x0 < 0 || y0 < 0 || x0 + 1 >= W || y0 + 1 >= H) continue;
        const a = at(R, x0, y0), b = at(R, x0 + 1, y0), c2 = at(R, x0, y0 + 1), d = at(R, x0 + 1, y0 + 1);
        if (a === d && b === c2 && a !== b) return false;
      }
      return true;
    }
    function outsideOK(R) {
      const seen = new Uint8Array(N), q = [];
      for (let c = 0; c < N; c++) {
        const x = c % W, y = (c / W) | 0;
        if (!R[c] && (x === 0 || y === 0 || x === W - 1 || y === H - 1)) { seen[c] = 1; q.push(c); }
      }
      while (q.length) { const c = q.pop(); const ns = nb(c); for (let i = 0; i < ns.length; i++) { const n = ns[i]; if (!R[n] && !seen[n]) { seen[n] = 1; q.push(n); } } }
      for (let c = 0; c < N; c++) if (!R[c] && !seen[c]) return false;
      return true;
    }
    for (;;) {
      const R = new Uint8Array(N);
      R[rnd(N)] = 1; let size = 1;
      const target = Math.floor(N * (0.45 + Math.random() * 0.17));
      let fails = 0;
      while (size < target && fails < N * 3) {
        const cand = [], wts = []; let tot = 0;
        for (let c = 0; c < N; c++) {
          if (R[c]) continue;
          const ns = nb(c); let k = 0; for (let i = 0; i < ns.length; i++) k += R[ns[i]];
          if (!k) continue;
          const w = k === 1 ? 5 : k === 2 ? 1.2 : 0.3;
          cand.push(c); wts.push(w); tot += w;
        }
        if (!cand.length) break;
        let r = Math.random() * tot, i = 0; while (r > wts[i]) { r -= wts[i]; i++; }
        const c = cand[Math.min(i, cand.length - 1)];
        R[c] = 1;
        if (diagOK(R, c) && outsideOK(R)) size++;
        else { R[c] = 0; fails++; }
      }
      if (size >= N * 0.35) return R;
    }
  }

  function solutionFromRegion(g, R) {
    const { W, H } = g; const sol = new Int8Array(g.E);
    const at = (x, y) => (x < 0 || y < 0 || x >= W || y >= H) ? 0 : R[y * W + x];
    for (let y = 0; y <= H; y++) for (let x = 0; x < W; x++) sol[g.hE(x, y)] = at(x, y - 1) !== at(x, y) ? 1 : -1;
    for (let y = 0; y < H; y++) for (let x = 0; x <= W; x++) sol[g.vE(x, y)] = at(x - 1, y) !== at(x, y) ? 1 : -1;
    return sol;
  }
  function cluesFromSolution(g, sol) {
    const cl = new Int8Array(g.C);
    for (let c = 0; c < g.C; c++) { let k = 0; for (let i = 0; i < 4; i++) if (sol[g.cellEdges[4 * c + i]] > 0) k++; cl[c] = k; }
    return cl;
  }

  function gradeSlither(g, clues) {
    for (let L = 1; L <= 3; L++) { const r = logicSolve(g, clues, L); if (r.solved) return L; }
    return 4;
  }

  function genSlither(W, H, level, budgetMs) {
    budgetMs = budgetMs || 8000;
    const g = geo(W, H); const t0 = Date.now();
    let best = null;
    for (let attempt = 0; attempt < 40; attempt++) {
      const sol = solutionFromRegion(g, makeRegion(W, H));
      const clues = cluesFromSolution(g, sol);
      const ok = (cl) => {
        const r = logicSolve(g, cl, level);
        if (!r.solved) return false;
        if (r.usedClose) return countSolutions(g, cl, 2) === 1;
        return true;
      };
      const order = shuffle(Array.from({ length: g.C }, (_, i) => i));
      for (const c of order) { const k = clues[c]; clues[c] = -1; if (!ok(clues)) clues[c] = k; }
      const grade = gradeSlither(g, clues);
      const res = { W, H, clues: Array.from(clues), sol: Array.from(sol), level: grade };
      if (grade === level) return res;
      if (!best || grade > best.level) best = res;
      if (Date.now() - t0 > budgetMs) break;
    }
    return best;
  }

  // ヒント：今の盤（正しい印だけ）から次に決まる1本。{edge, val, level} か null
  function slitherHint(W, H, clues, marks) {
    const g = geo(W, H);
    const ctx = { g, clues, qc: [], qv: [], log: [] };
    const s = newState(g);
    for (let e = 0; e < g.E; e++) if (marks[e]) { if (!setE(ctx, s, e, marks[e])) return null; }
    ctx.log = [];
    seedQueue(ctx);
    if (propagate(ctx, s) === 0) return null;
    const pick = (log) => { for (const x of log) { if (x >= 0) return { edge: x, val: 1 }; } return log.length ? { edge: ~log[0], val: -1 } : null; };
    if (ctx.log.length) { const h = pick(ctx.log); if (h) { h.level = 1; return h; } }
    for (const lim of [L2LIM, Infinity]) {
      for (let e = 0; e < g.E; e++) {
        if (s.e[e] !== 0) continue;
        for (let t = 0; t < 2; t++) {
          const val = t === 0 ? 1 : -1;
          const ts = cloneState(s); const tctx = { g, clues, qc: [], qv: [], budget: lim };
          let contra = false;
          if (!setE(tctx, ts, e, val)) contra = ts.bad; else contra = propagate(tctx, ts) === 0;
          if (contra) return { edge: e, val: -val, level: lim === L2LIM ? 2 : 3 };
        }
      }
    }
    return null;
  }

  /* ================= マインスイーパー ================= */
  function nbrs(W, H, c) {
    const x = c % W, y = (c / W) | 0, r = [];
    for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
      if (!dx && !dy) continue; const nx = x + dx, ny = y + dy;
      if (nx >= 0 && ny >= 0 && nx < W && ny < H) r.push(ny * W + nx);
    }
    return r;
  }
  const nbCache = {};
  function nbTable(W, H) {
    const k = W + 'x' + H; if (nbCache[k]) return nbCache[k];
    const t = []; for (let c = 0; c < W * H; c++) t.push(nbrs(W, H, c));
    return (nbCache[k] = t);
  }
  function numbersOf(W, H, mines) {
    const N = W * H, nb = nbTable(W, H), num = new Int8Array(N);
    for (let c = 0; c < N; c++) { let k = 0; const ns = nb[c]; for (let i = 0; i < ns.length; i++) k += mines[ns[i]]; num[c] = k; }
    return num;
  }

  const ENUM_CAP = 26;

  // st: 0=未知 1=開いた 2=地雷と分かった。決まるものを {safe:[], mine:[], tier} で返す
  function mineDeduce(W, H, st, num, M) {
    const N = W * H, nb = nbTable(W, H);
    const safe = new Set(), mine = new Set();
    const cons = []; // {cells, r}
    const consOf = new Map();
    for (let c = 0; c < N; c++) {
      if (st[c] !== 1) continue;
      const ns = nb[c]; const u = []; let k = 0;
      for (let i = 0; i < ns.length; i++) { const n = ns[i]; if (st[n] === 0) u.push(n); else if (st[n] === 2) k++; }
      if (!u.length) continue;
      const r = num[c] - k;
      if (r === 0) u.forEach(x => safe.add(x));
      else if (r === u.length) u.forEach(x => mine.add(x));
      const idx = cons.length; cons.push({ cells: u, r });
      for (const x of u) { if (!consOf.has(x)) consOf.set(x, []); consOf.get(x).push(idx); }
    }
    if (safe.size || mine.size) return { safe: [...safe], mine: [...mine], tier: 1 };
    // 2つの数字の組み合わせ
    for (let i = 0; i < cons.length; i++) {
      const A = cons[i]; const setA = new Set(A.cells);
      const others = new Set(); for (const x of A.cells) for (const j of consOf.get(x)) if (j !== i) others.add(j);
      for (const j of others) {
        const B = cons[j];
        const onlyA = A.cells.filter(x => !B.cells.includes(x));
        const onlyB = B.cells.filter(x => !setA.has(x));
        const common = A.cells.length - onlyA.length;
        const lo = Math.max(0, A.r - onlyA.length, B.r - onlyB.length);
        const hi = Math.min(common, A.r, B.r);
        if (onlyB.length) {
          if (B.r - hi === onlyB.length) onlyB.forEach(x => mine.add(x));
          if (B.r - lo === 0) onlyB.forEach(x => safe.add(x));
        }
      }
    }
    if (safe.size || mine.size) return { safe: [...safe], mine: [...mine], tier: 2 };
    // 境目のマスを全部調べる（残りの地雷の数も使う）
    let known = 0, unknownAll = 0; for (let c = 0; c < N; c++) { if (st[c] === 2) known++; else if (st[c] === 0) unknownAll++; }
    const R = M - known;
    const frontier = [...consOf.keys()];
    const interior = unknownAll - frontier.length;
    const seen = new Set(); const comps = [];
    for (const f of frontier) {
      if (seen.has(f)) continue;
      const comp = []; const q = [f]; seen.add(f);
      while (q.length) {
        const x = q.shift(); comp.push(x);
        for (const j of consOf.get(x)) for (const y of cons[j].cells) if (!seen.has(y)) { seen.add(y); q.push(y); }
      }
      comps.push(comp);
    }
    const tooBig = comps.some(c => c.length > ENUM_CAP);
    const res = []; // per comp: {cells, sols: [{m, bits(Uint8Array)}]}
    for (const comp of comps) {
      if (comp.length > ENUM_CAP) { res.push(null); continue; }
      const pos = new Map(comp.map((x, i) => [x, i]));
      const cidx = [...new Set(comp.flatMap(x => consOf.get(x)))];
      const cc = cidx.map(j => ({ cells: cons[j].cells.map(x => pos.get(x)), r: cons[j].r }));
      const consOfLocal = comp.map(() => []);
      cc.forEach((k, j) => k.cells.forEach(i => consOfLocal[i].push(j)));
      const val = new Int8Array(comp.length).fill(-1);
      const sum = new Int32Array(cc.length), left = new Int32Array(cc.length);
      cc.forEach((k, j) => { left[j] = k.cells.length; });
      const sols = []; let nodes = 0; let aborted = false;
      (function rec(i, m) {
        if (aborted) return;
        if (++nodes > 200000) { aborted = true; return; }
        if (i === comp.length) { sols.push({ m, bits: Uint8Array.from(val) }); return; }
        for (let v = 0; v <= 1; v++) {
          let ok = true;
          for (const j of consOfLocal[i]) { sum[j] += v; left[j]--; if (sum[j] > cc[j].r || sum[j] + left[j] < cc[j].r) ok = false; }
          if (ok && m + v <= R) { val[i] = v; rec(i + 1, m + v); }
          for (const j of consOfLocal[i]) { sum[j] -= v; left[j]++; }
          val[i] = -1;
        }
      })(0, 0);
      res.push(aborted ? null : { cells: comp, sols });
    }
    const allOK = !tooBig && res.every(Boolean);
    if (allOK) {
      // 他の部分の地雷数の取りうる値（boolean畳み込み）
      const sets = res.map(r => { const s = new Set(r.sols.map(x => x.m)); return s; });
      const conv = (list) => { let acc = new Set([0]); for (const s of list) { const n = new Set(); for (const a of acc) for (const b of s) if (a + b <= R) n.add(a + b); acc = n; } return acc; };
      const feasibleTotal = (t) => (interior === 0 ? t === R : (t <= R && R - t <= interior));
      let anyInteriorSafe = false, anyInteriorMine = false, anyFeasible = false;
      res.forEach((r, k) => {
        const others = conv(sets.filter((_, i) => i !== k));
        const okS = r.sols.filter(sl => { for (const o of others) if (feasibleTotal(sl.m + o)) return true; return false; });
        if (!okS.length) return;
        r.cells.forEach((cell, i) => {
          let all1 = true, all0 = true;
          for (const sl of okS) { if (sl.bits[i]) all0 = false; else all1 = false; }
          if (all1) mine.add(cell); if (all0) safe.add(cell);
        });
      });
      if (interior > 0) {
        for (const t of conv(sets)) {
          if (!feasibleTotal(t)) continue; anyFeasible = true;
          if (R - t > 0) anyInteriorMine = true; if (R - t < interior) anyInteriorSafe = true;
        }
        if (anyFeasible && (!anyInteriorMine || !anyInteriorSafe)) {
          for (let c = 0; c < N; c++) if (st[c] === 0 && !consOf.has(c)) (anyInteriorMine ? mine : safe).add(c);
        }
      }
    } else {
      res.forEach(r => {
        if (!r || !r.sols.length) return;
        r.cells.forEach((cell, i) => {
          let all1 = true, all0 = true;
          for (const sl of r.sols) { if (sl.bits[i]) all0 = false; else all1 = false; }
          if (all1) mine.add(cell); if (all0) safe.add(cell);
        });
      });
    }
    if (frontier.length === 0 && unknownAll > 0) { // 境目が無い（全部閉じている）とき
      if (R === 0) for (let c = 0; c < N; c++) if (st[c] === 0) safe.add(c);
      if (R === unknownAll) for (let c = 0; c < N; c++) if (st[c] === 0) mine.add(c);
    }
    return { safe: [...safe], mine: [...mine], tier: 3 };
  }

  function openCell(W, H, st, num, c) {
    const nb = nbTable(W, H); const q = [c];
    if (st[c] !== 0) return;
    st[c] = 1;
    while (q.length) {
      const x = q.pop();
      if (num[x] !== 0) continue;
      for (const n of nb[x]) if (st[n] === 0) { st[n] = 1; q.push(n); }
    }
  }

  function mineSolve(W, H, mines, M, first) {
    const N = W * H, num = numbersOf(W, H, mines), st = new Int8Array(N);
    openCell(W, H, st, num, first);
    for (;;) {
      let opened = 0; for (let c = 0; c < N; c++) if (st[c] === 1) opened++;
      if (opened === N - M) return { ok: true, st };
      const d = mineDeduce(W, H, st, num, M);
      if (!d.safe.length && !d.mine.length) return { ok: false, st };
      for (const c of d.mine) { if (!mines[c]) throw new Error('solver bug (mine)'); st[c] = 2; }
      for (const c of d.safe) { if (mines[c]) throw new Error('solver bug'); openCell(W, H, st, num, c); }
    }
  }

  function genMines(W, H, M, first, budgetMs) {
    budgetMs = budgetMs || 6000;
    const N = W * H, nb = nbTable(W, H), t0 = Date.now();
    const banned = new Uint8Array(N); banned[first] = 1;
    if (N - 9 >= M) for (const n of nb[first]) banned[n] = 1;
    let lastMines = null;
    while (Date.now() - t0 < budgetMs) {
      const mines = new Uint8Array(N);
      const pool = []; for (let c = 0; c < N; c++) if (!banned[c]) pool.push(c);
      shuffle(pool); for (let i = 0; i < M; i++) mines[pool[i]] = 1;
      for (let iter = 0; iter < N; iter++) {
        const r = mineSolve(W, H, mines, M, first);
        if (r.ok) return { W, H, M, mines: Array.from(mines), first, noGuess: true, tries: iter };
        lastMines = mines;
        const st = r.st;
        const front = [], inner = [];
        for (let c = 0; c < N; c++) {
          if (st[c] !== 0 || banned[c]) continue;
          let f = false; for (const n of nb[c]) if (st[n] === 1) { f = true; break; }
          (f ? front : inner).push(c);
        }
        const fm = front.filter(c => mines[c]);
        const free = inner.filter(c => !mines[c]);
        if (!fm.length || !free.length) break;
        const a = fm[rnd(fm.length)], b = free[rnd(free.length)];
        mines[a] = 0; mines[b] = 1;
        if (Date.now() - t0 > budgetMs) break;
      }
    }
    return { W, H, M, mines: Array.from(lastMines), first, noGuess: false };
  }

  const api = { geo, genSlither, logicSolve, countSolutions, gradeSlither, slitherHint, cluesFromSolution, genMines, mineDeduce, numbersOf, nbTable, openCell };
  root.EPGen = api;
  if (typeof module !== 'undefined' && module.exports) module.exports = api;

  // Worker として動いているとき
  if (typeof WorkerGlobalScope !== 'undefined' && root instanceof WorkerGlobalScope) {
    root.onmessage = function (ev) {
      const m = ev.data;
      try {
        if (m.type === 'slither') root.postMessage({ id: m.id, type: m.type, key: m.key, puzzle: genSlither(m.W, m.H, m.level) });
        else if (m.type === 'mine') root.postMessage({ id: m.id, type: m.type, puzzle: genMines(m.W, m.H, m.M, m.first) });
      } catch (err) { root.postMessage({ id: m.id, type: m.type, key: m.key, error: String(err && err.stack || err) }); }
    };
  }
})(typeof self !== 'undefined' ? self : globalThis);
