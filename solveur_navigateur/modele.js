/* Solveur HiGHS du gestionnaire (Citadelle) — modèle mathématique et amélioration par fenêtres.
   Porté le 17/11/2026 depuis solveur_code/solveur_v17 (solveur_tout.js, regles_v8.js, regles_v10.js, regles_v10_defs.js,
   regles_demi.js, lns.js) : même modèle, mêmes poids, mais la période (un mois ou un trimestre) remplace le T1 2027 écrit en dur,
   et les données arrivent en paramètre (aucun fichier). Utilisable dans un worker du navigateur et sous Node (tests).

   Entrée E (fabriquée par solveurExtraire() dans le gestionnaire) : mois ['AAAA-MM', …], debut, jours, info, demande [{dk,pid,m}],
   elig/forcables/chainables [[ci, docId]], souhaits, autour/fixes [{dk,pid,doc}], docs [...], heures, vendredi, dow, ferie,
   noms [{local_id,lastname,special_case,extra_profile,contract_start,contract_end}], indispos.
   Une solution : { objectif, affectations {dk:{pid:doc}}, trous [{dk,pid}], forces, demi [{dk,pid,doc,heures,second}] }. */
(function (racine, fabrique) {
  if (typeof module === 'object' && module.exports) module.exports = fabrique();
  else racine.SolveurModele = fabrique();
}(typeof self !== 'undefined' ? self : this, function () {
  'use strict';
  const WEQ = ['we-coord', 'we-satmu', 'we-smur-sat', 'we-smur-sun'], VN = ['coord-n', 'smur-n', 'satmu-n'], VS = ['pm14', 'pm16'], SMUR = ['smur-n', 'we-smur-sat', 'we-smur-sun'];
  const DOUB = ['doub-coord', 'doub-smur', 'doubl-u-ad', 'doubl-u-bc'];
  const POIDS = { souhait: 1500, prioPH: 2, prioMG: 1, prioAsst: 4, quotaSeul: 5, vendEq: 8, trou: 10000, quota: 2000, oblig: 200, smur: 60, smurSous: 30, sem: 10, weT: 12, weM: 3, vend2: 6, vendSoir: 4,
    chaine: 30, toujours: 30, demi: 250, heure: 2, doubSoft: 5, equite: 1, smurnA: 500 };
  const dayN = dk => Math.round(new Date(dk + 'T12:00:00Z').getTime() / 864e5);
  const isoWeek = dk => { const d = new Date(dk + 'T12:00:00Z'); const t = new Date(Date.UTC(d.getUTCFullYear(), d.getUTCMonth(), d.getUTCDate())); const n = (t.getUTCDay() + 6) % 7; t.setUTCDate(t.getUTCDate() - n + 3); return t.getUTCFullYear() * 100 + Math.ceil(((t - new Date(Date.UTC(t.getUTCFullYear(), 0, 1))) / 864e5 + 1) / 7); };
  const nxt = (dk, k) => { const t = new Date(dk + 'T12:00:00Z'); t.setUTCDate(t.getUTCDate() + k); return t.toISOString().slice(0, 10); };

  /* Construit le texte LP du modèle. opts : { init (solution), deb, fin (fenêtre libre ; hors fenêtre tout est figé sur init) } */
  function construire(E, opts) {
    opts = opts || {};
    const W = Object.assign({}, POIDS, opts.poids || {});
    const M = E.mois.map((_, i) => i), mi = dk => E.mois.indexOf(String(dk).slice(0, 7));
    const enPeriode = dk => mi(dk) >= 0;
    const I = pid => E.info[pid] || {};
    const NOMS = E.noms || [];
    const nomDe = d => ((NOMS.find(r => r.local_id === d) || {}).lastname || '').toUpperCase();
    const log = [];
    const xv = E.elig.map(([ci, d]) => ({ ci, d, force: false })).concat(E.forcables.map(([ci, d]) => ({ ci, d, force: true })))
      .concat((E.chainables || []).map(([ci, d]) => ({ ci, d, force: false, chain: true }))).map((p, k) => ({ k, ci: p.ci, d: p.d, force: p.force, chain: !!p.chain, c: E.demande[p.ci], n: 'x' + k }));
    const parDoc = {}; xv.forEach(v => (parDoc[v.d] = parDoc[v.d] || []).push(v));
    const parCase = {}; xv.forEach(v => (parCase[v.ci] = parCase[v.ci] || []).push(v));
    const L = [], obj = {}, bin = xv.map(v => v.n), gen = [];
    const addObj = (n, c) => { obj[n] = (obj[n] || 0) + c; };
    const somme = vs => vs.map(v => v.n).join(' + ');
    let nc = 0; const C = (expr, rhs) => L.push(' c' + (nc++) + ': ' + expr + ' ' + rhs);
    const ecart = (vs, cible, poids, constante) => { if (cible == null || !vs.length) return; const p = 'p' + nc, m = 'm' + nc; C(somme(vs) + ' - ' + p + ' + ' + m, '= ' + (cible - (constante || 0))); gen.push(p, m); addObj(p, poids); addObj(m, poids); };
    const surplus = (vs, borne, poids) => { if (!vs.length || vs.length <= borne) return; const z = 'z' + nc; C(somme(vs) + ' - ' + z, '<= ' + borne); gen.push(z); addObj(z, poids); };
    const manque = (vs, borne, poids) => { if (borne <= 0) return; const u = 'u' + nc; C((vs.length ? somme(vs) + ' + ' : '') + u, '>= ' + borne); gen.push(u); addObj(u, poids); };
    const CHAINES = [['coord', 'coord-n'], ['b', 'smur-n'], ['a', 'satmu-n'], ['admin', 'coord-n'], ['admin', 'smur-n'], ['admin', 'satmu-n']];
    const chaine = (p, q) => CHAINES.some(([a, b]) => (a === p && b === q) || (a === q && b === p));
    const docE = id => E.docs.find(x => x.id === id) || { regles: [], parMois: M.map(() => ({})) };
    const pm = (D, m) => (D.parMois || [])[m] || {};

    // nuit chaînable : seulement avec le poste de jour du même médecin
    { const JD = { 'coord-n': 'coord', 'satmu-n': 'a', 'smur-n': 'b' };
      xv.filter(v => v.chain).forEach(v => { const j = (parDoc[v.d] || []).find(w => !w.chain && w.c.dk === v.c.dk && w.c.pid === JD[v.c.pid]); C(v.n + (j ? ' - ' + j.n : ''), '<= 0'); }); }
    // 1. couverture
    E.demande.forEach((c, ci) => { const vs = parCase[ci] || []; C((vs.length ? somme(vs) + ' + ' : '') + 't' + ci, '= 1'); bin.push('t' + ci); addObj('t' + ci, W.trou); });
    const sansDirect = new Set(E.forcables.map(([, d]) => d).filter(d => !E.elig.some(([, e]) => e === d)));
    xv.forEach(v => { if (v.force) addObj(v.n, sansDirect.has(v.d) ? W.quotaSeul : W.quota); });
    // 2. par médecin : même jour, repos, espacement des gardes, contexte fixe
    const I0d = (opts.init && opts.init.affectations) || null; const tient = v => !!I0d && (I0d[v.c.dk] || {})[v.c.pid] === v.d; let toleresRepos = 0;
    Object.entries(parDoc).forEach(([dS, vs]) => { const d = +dS;
      const fix = E.autour.filter(a => a.doc == d);
      const parJour = {}; vs.forEach(v => (parJour[v.c.dk] = parJour[v.c.dk] || []).push(v));
      const jourFix = {}; fix.forEach(a => (jourFix[a.dk] = jourFix[a.dk] || []).push(a.pid));
      vs.forEach(v => { const dk = v.c.dk, pid = v.c.pid;
        if ((jourFix[dk] || []).some(q => !chaine(q, pid))) { C(v.n, '= 0'); return; }
        if ((jourFix[nxt(dk, -1)] || []).some(q => I(q).repos)) { C(v.n, '= 0'); return; }
        if (E.dow[dk] === 0 && (jourFix[nxt(dk, -2)] || []).some(q => I(q).reposDim)) { C(v.n, '= 0'); return; }
        if (I(pid).repos && (jourFix[nxt(dk, 1)] || []).length) { C(v.n, '= 0'); return; }
        if (I(pid).reposDim && E.dow[dk] === 5 && (jourFix[nxt(dk, 2)] || []).length) { C(v.n, '= 0'); return; }
        if (I(pid).garde && fix.some(a => I(a.pid).garde && Math.abs(dayN(dk) - dayN(a.dk)) <= 2 && a.dk !== dk)) { C(v.n, '= 0'); return; }
      });
      const D = docE(d); const noChain = (D.regles || []).filter(r => r.type === 'no_chain').flatMap(r => r.posts || []);
      Object.values(parJour).forEach(js => { for (let a = 0; a < js.length; a++) for (let b = a + 1; b < js.length; b++) { const p = js[a].c.pid, q = js[b].c.pid;
        if (!chaine(p, q) || noChain.includes(p) || noChain.includes(q)) C(js[a].n + ' + ' + js[b].n, '<= 1'); } });
      const wJour = {}; const travaille = (js, r) => { const key = js[0].c.dk; let w = wJour[key]; if (!w) { w = 'w' + d + '_' + key.replace(/-/g, ''); wJour[key] = w; gen.push(w); L.push(' b' + w + ': ' + w + ' <= 1'); js.forEach(v => C(v.n + ' - ' + w, '<= 0')); }
        // [17/11] tolérance du départ : repos déjà enfreint par le planning de départ (même médecin, même jour) → toléré ici seulement
        if (tient(r) && js.some(tient)) { toleresRepos++; return; }
        C(r.n + ' + ' + w, '<= 1'); };
      Object.entries(parJour).forEach(([dk, js]) => { js.filter(v => I(v.c.pid).repos).forEach(r => {
        const suiv = parJour[nxt(dk, 1)] || []; if (suiv.length) travaille(suiv, r);
        if (I(r.c.pid).reposDim && E.dow[dk] === 5) { const dim = parJour[nxt(dk, 2)] || []; if (dim.length) travaille(dim, r); } }); });
      const g = vs.filter(v => I(v.c.pid).garde); const gj = {}; g.forEach(v => (gj[dayN(v.c.dk)] = gj[dayN(v.c.dk)] || []).push(v));
      Object.keys(gj).map(Number).forEach(j => { const w = [j, j + 1, j + 2].flatMap(x => gj[x] || []); if (w.length > 1) C(somme(w), '<= 1'); });
    });
    // 2b. Circuit le lundi et le mardi réservé à quelques médecins (liste du gestionnaire)
    const CIRC_LM = ['DEGESVES', 'BUSCH', 'VAN BRUSSEL', 'STECKX'];
    xv.forEach(v => { if (v.c.pid === 'circuit' && (E.dow[v.c.dk] === 1 || E.dow[v.c.dk] === 2) && !CIRC_LM.includes(nomDe(v.d))) C(v.n, '= 0'); });
    // demi-garde de WE de jour (règle de fiche we_half_day_month) ; HX = termes d'heures ajoutés en section 3
    const HX = {}; const DEMI = demiGarde({ E, W, parDoc, parCase, C, addObj, gen, bin, I, dayN, nxt, mi, M, HX, init: opts.init, deb: opts.deb, fin: opts.fin, log });
    // 3. heures, gardes, règles individuelles, doublures
    const eligCount = {}; xv.forEach(v => { if (!v.force) { const k = v.d + '|' + v.c.pid; eligCount[k] = (eligCount[k] || 0) + 1; } });
    E.docs.forEach(D => { const vs = parDoc[D.id] || []; if (!vs.length) return;
      const fx = E.autour.filter(a => a.doc == D.id && enPeriode(a.dk));
      const hExpr = vs.map(v => E.heures[v.ci] + ' ' + v.n).join(' + ') + (HX[D.id] ? ' ' + HX[D.id].join(' ') : '');
      C(hExpr, '<= ' + Math.max(0, D.maxH - D.fixeH));
      if (D.cibleQ > 0) { const T = D.cibleQ, tr = 0.05 * T, segs = []; for (let k = 0; k < 8; k++) { const s = 's' + nc + '_' + k; segs.push(s); gen.push(s); addObj(s, W.heure * (/^Assistant/.test(D.role) ? W.prioAsst : /^PH/.test(D.role) ? W.prioPH : W.prioMG) * (k + 1) * 100 / T * (1 / 5)); }
        const o = 'o' + nc; gen.push(o); addObj(o, W.heure * 100 / T * (1 / 5));
        C(hExpr + ' + ' + segs.join(' + ') + ' - ' + o, '= ' + Math.round((T - D.fixeH) * 100) / 100);
        segs.slice(0, 7).forEach(s => L.push(' b' + s + ': ' + s + ' <= ' + Math.round(tr * 100) / 100)); }
      M.forEach(m => { const vm = vs.filter(v => v.c.m === m), fm = fx.filter(a => mi(a.dk) === m), q = pm(D, m);
        { const gc = vm.filter(v => I(v.c.pid).maxG); if (D.cap != null && gc.length) C(somme(gc), '<= ' + Math.max(0, D.cap - fm.filter(a => I(a.pid).maxG).length)); }
        const sem = vm.filter(v => I(v.c.pid).semaine); if (q.wd != null && sem.length) C(somme(sem), '<= ' + Math.max(0, q.wd + 1 - fm.filter(a => I(a.pid).semaine).length));
        if (D.maxG != null) { const x = vm.filter(v => I(v.c.pid).maxG); if (x.length) C(somme(x), '<= ' + Math.max(0, D.maxG - fm.filter(a => I(a.pid).maxG).length)); }
        ecart(sem, q.wd, W.sem); ecart(vm.filter(v => WEQ.includes(v.c.pid)), q.we, W.weM);
        const vn = vm.filter(v => E.vendredi[v.ci] && VN.concat(['n16']).includes(v.c.pid)), vsr = vm.filter(v => E.vendredi[v.ci] && VS.includes(v.c.pid));
        surplus(vn, 1, W.vend2); if (vn.length && vsr.length) surplus(vn.concat(vsr), 1, W.vendSoir);
        const sm = vm.filter(v => SMUR.includes(v.c.pid) && !v.force); const smFix = fm.filter(a => SMUR.includes(a.pid)).length;
        if (sm.length) { surplus(sm, Math.max(0, 1 - smFix), W.smur); if (!smFix) manque(sm, 1, W.smurSous); }
        if (D.role === 'Assistant SMUR ok') { const sn = vm.filter(v => v.c.pid === 'smur-n'); if (sn.length) manque(sn, 1, W.smurnA); }
        if (!/^PH|^Assistant/.test(D.role) && !(D.regles || []).some(r => r.type === 'max_post_per_month' && (r.posts || []).includes('pm14'))) { const x = vm.filter(v => v.c.pid === 'pm14'); const deja = fm.filter(a => a.pid === 'pm14').length; if (x.length > Math.max(0, 4 - deja)) C(somme(x), '<= ' + Math.max(0, 4 - deja)); }
        (D.regles || []).forEach(r => { const posts = r.posts || [];
          if (r.type === 'max_post_per_month') { const x = vm.filter(v => posts.includes(v.c.pid)); if (x.length) C(somme(x), '<= ' + Math.max(0, (r.count != null ? r.count : 1) - fm.filter(a => posts.includes(a.pid)).length)); }
          if (r.type === 'monthly_post_mandatory') { const okJ = dk => r.dayFilter !== 'weekday' || (E.dow[dk] >= 1 && E.dow[dk] <= 5 && !E.ferie.includes(dk));
            const x = vm.filter(v => posts.includes(v.c.pid) && okJ(v.c.dk)); const deja = fm.filter(a => posts.includes(a.pid) && okJ(a.dk)).length; if (x.length) manque(x, (r.count != null ? r.count : 1) - deja, W.oblig); }
          if (r.type === 'we_saturday_mandatory') { const x = vm.filter(v => posts.includes(v.c.pid) && E.dow[v.c.dk] === 6); const deja = fm.filter(a => posts.includes(a.pid) && E.dow[a.dk] === 6).length; if (x.length) manque(x, (r.count != null ? r.count : 1) - deja, W.oblig); }
        });
      });
      const weT = (D.parMois || []).reduce((a, q) => a + ((q || {}).we || 0), 0) - fx.filter(a => WEQ.includes(a.pid)).length; if ((D.parMois || []).some(q => q && q.we != null)) ecart(vs.filter(v => WEQ.includes(v.c.pid)), Math.max(0, weT), W.weT);
      const db = vs.filter(v => v.c.pid === 'we-doublure'), dbF = fx.filter(a => a.pid === 'we-doublure').length;
      if (D.fenetreDoublure === 'quarter' && db.length) C(somme(db), '<= ' + Math.max(0, 1 - dbF));
      if (D.fenetreDoublure === 'month') M.forEach(m => { const x = db.filter(v => v.c.m === m); if (x.length) C(somme(x), '<= 1'); });
      (D.regles || []).forEach(r => { const posts = r.posts || [];
        if (r.type === 'max_post_per_quarter') { const x = vs.filter(v => posts.includes(v.c.pid)); if (x.length) C(somme(x), '<= ' + Math.max(0, (r.count != null ? r.count : 1) - fx.filter(a => posts.includes(a.pid)).length)); }
        if (r.type === 'weekly_exclusive_group') { const sw = {}; vs.filter(v => posts.includes(v.c.pid)).forEach(v => (sw[isoWeek(v.c.dk)] = sw[isoWeek(v.c.dk)] || []).push(v));
          Object.entries(sw).forEach(([w, x]) => { const deja = fx.filter(a => posts.includes(a.pid) && isoWeek(a.dk) == w).length; C(somme(x), '<= ' + Math.max(0, (r.count != null ? r.count : 2) - deja)); }); }
        if (r.type === 'mandatory_chain') [['coord', 'coord-n'], ['a', 'satmu-n'], ['b', 'smur-n']].forEach(([p, q]) => vs.filter(v => v.c.pid === p).forEach(v => {
          const nuit = vs.find(w => w.c.dk === v.c.dk && w.c.pid === q); const z = 'z' + nc; C(v.n + (nuit ? ' - ' + nuit.n : '') + ' - ' + z, '<= 0'); gen.push(z); addObj(z, W.chaine); }));
        if (r.type === 'linked_post' && r.triggerPost && r.linkedPost) vs.filter(v => v.c.pid === r.triggerPost).forEach(v => {
          const lien = vs.find(w => w.c.dk === v.c.dk && w.c.pid === r.linkedPost); if (!lien) return; const z = 'z' + nc; C(v.n + ' - ' + lien.n + ' - ' + z, '<= 0'); gen.push(z); addObj(z, W.chaine); });
        if (r.type === 'always_schedule') { const pj = {}; vs.forEach(v => { if (E.dow[v.c.dk] >= 1 && E.dow[v.c.dk] <= 5) (pj[v.c.dk] = pj[v.c.dk] || []).push(v); });
          Object.entries(pj).forEach(([dk, x]) => { if (!fx.some(a => a.dk === dk)) manque(x, 1, W.toujours); }); }
      });
      DOUB.forEach(p => { const x = vs.filter(v => v.c.pid === p); if (!x.length) return; const nm = E.mois.length / 3, dur = Math.ceil((p === 'doub-coord' ? 12 : 20) * nm), mou = Math.ceil((p === 'doub-coord' ? 9 : 15) * nm);
        if (x.length > dur) C(somme(x), '<= ' + dur); surplus(x, mou, W.doubSoft);
        const pj = {}; x.forEach(v => { pj[dayN(v.c.dk)] = v; }); Object.keys(pj).map(Number).forEach(j => { if (pj[j + 1]) C(pj[j].n + ' + ' + pj[j + 1].n, '<= 1'); }); });
      const dw = {}; vs.filter(v => DOUB.includes(v.c.pid)).forEach(v => (dw[isoWeek(v.c.dk)] = dw[isoWeek(v.c.dk)] || []).push(v)); Object.values(dw).forEach(x => { if (x.length > 3) C(somme(x), '<= 3'); });
      if (D.role === 'Assistant SMUR ok') { const x = vs.filter(v => v.c.pid === 'smur-j'); const cap = Math.ceil(4 * E.mois.length / 3); if (x.length > cap) C(somme(x), '<= ' + cap); }
    });
    reglesV8({ E, W, xv, parDoc, C, addObj, gen, bin, somme, isoWeek, dayN, nomDe, NOMS, I, mi, M, enPeriode, log, tient: I0d ? tient : null });
    reglesV10({ E, W, xv, parDoc, C, addObj, gen, bin, somme, NOMS, mi, M, enPeriode, log });
    // 4. équilibres des nuits du vendredi (au prorata des heures)
    const vnAll = xv.filter(v => !v.force && E.vendredi[v.ci] && VN.includes(v.c.pid)); const totVN = E.demande.filter((c, ci) => E.vendredi[ci] && VN.includes(c.pid)).length;
    const docsVN = [...new Set(vnAll.map(v => v.d))]; const fte = d => Math.max(0.1, ((E.docs.find(x => x.id == d) || {}).h || 40) / 40); const sH = docsVN.reduce((a, d) => a + fte(d), 0);
    docsVN.forEach(d => ecart(vnAll.filter(v => v.d == d), Math.round(totVN * fte(d) / sH * 100) / 100, W.vendEq));
    // 5. équité par poste dans chaque grade
    const EQ = Object.keys(E.info).filter(p => !['admin', 'circuit'].includes(p) && (I(p).section === 'jour' || ['pm14', 'we-e', 'we-u3-sat', 'we-u3-sun', 'we-doublure', 'n16'].includes(p)));
    const gradeDe = d => { const r = (E.docs.find(x => x.id === d) || {}).role || ''; return /^PH/.test(r) ? 'PH' : /^Assistant/.test(r) ? 'ASS' : 'MG'; };
    EQ.forEach(p => { const ds = [...new Set(xv.filter(v => v.c.pid === p && !v.force).map(v => v.d))]; const gr = {}; ds.forEach(d => (gr[gradeDe(d)] = gr[gradeDe(d)] || []).push(d));
      Object.values(gr).forEach(g => { if (g.length < 2) return; const tot = g.reduce((a, d) => a + (eligCount[d + '|' + p] || 0), 0); const tousG = xv.filter(v => v.c.pid === p && g.includes(v.d));
        g.forEach(d => { const r = (eligCount[d + '|' + p] || 0) / tot; const own = xv.filter(v => v.c.pid === p && v.d === d); const pp = 'p' + nc, mm = 'm' + nc;
          C(own.map(v => (1 - r).toFixed(4) + ' ' + v.n).concat(tousG.filter(v => v.d !== d).map(v => '- ' + r.toFixed(4) + ' ' + v.n)).join(' + ').split('+ - ').join('- ') + ' - ' + pp + ' + ' + mm, '= 0'); gen.push(pp, mm); addObj(pp, W.equite); addObj(mm, W.equite); }); }); });
    // [17/11] TOLÉRANCE DU DÉPART : une contrainte stricte qui ne porte que sur des affectations (x) et des trous (t), et que le planning
    // de départ (celui du moteur) enfreint, est assouplie au niveau atteint par ce planning — jamais au-delà. Le départ reste donc
    // toujours faisable et le solveur ne peut pas faire pire que le moteur sur ces règles (ex. 14-22 et WE-E à moins de 72 h).
    let toleres = 0; const tolereEx = [];
    if (opts.init) { const I0 = opts.init.affectations || {}; const val = {};
      xv.forEach(v => { val[v.n] = ((I0[v.c.dk] || {})[v.c.pid] === v.d) ? 1 : 0; });
      E.demande.forEach((c, ci) => { const d0 = (I0[c.dk] || {})[c.pid]; val['t' + ci] = (d0 != null && (parCase[ci] || []).some(v => v.d === d0)) ? 0 : 1; });
      for (let i = 0; i < L.length; i++) { const m = /^ (c\d+): (.*) (<=|>=|=) (-?[\d.]+(?:e[+-]?\d+)?)$/.exec(L[i]); if (!m) continue;
        let lhs = 0, signe = 1, coef = 1, ok = true;
        for (const tk of m[2].split(' ')) { if (!tk) continue; if (tk === '+') { signe = 1; continue; } if (tk === '-') { signe = -1; continue; }
          if (/^-?[\d.]+(?:e[+-]?\d+)?$/.test(tk)) { coef = +tk; continue; } if (!(tk in val)) { ok = false; break; } lhs += signe * coef * val[tk]; signe = 1; coef = 1; }
        if (!ok) continue; const rhs = +m[4], op = m[3];
        const viole = op === '<=' ? lhs > rhs + 1e-6 : op === '>=' ? lhs < rhs - 1e-6 : Math.abs(lhs - rhs) > 1e-6; if (!viole) continue;
        const nop = op === '=' ? (lhs > rhs ? '<=' : '>=') : op; L[i] = ' ' + m[1] + ': ' + m[2] + ' ' + nop + ' ' + (Math.round(lhs * 10000) / 10000); toleres++;
        if (tolereEx.length < 20) tolereEx.push(m[1] + ' ' + op + ' ' + rhs + ' → ' + lhs); } }
    // fenêtre libre : hors [deb, fin], tout est figé sur la solution de départ
    if (opts.init && opts.deb) { const I0 = opts.init.affectations || {}; const libre = c => c.dk >= opts.deb && c.dk <= opts.fin;
      xv.forEach(v => { if (libre(v.c)) return; C(v.n, '= ' + (((I0[v.c.dk] || {})[v.c.pid]) === v.d ? 1 : 0)); });
      E.demande.forEach((c, ci) => { if (libre(c)) return; const d0 = (I0[c.dk] || {})[c.pid]; const tenu = d0 != null && (parCase[ci] || []).some(v => v.d === d0); C('t' + ci, '= ' + (tenu ? 0 : 1)); }); }
    // 6. souhaits et départage
    const souh = new Set(E.souhaits.map(([ci, d]) => ci + '|' + d));
    xv.forEach(v => addObj(v.n, souh.has(v.ci + '|' + v.d) ? -W.souhait : ((v.k * 7919) % 97 / 1000 + 0.001)));
    const NL = '\n';
    const objTxt = Object.entries(obj).filter(([, c]) => c !== 0).map(([n, c]) => (c < 0 ? '- ' : '+ ') + Math.abs(Math.round(c * 10000) / 10000) + ' ' + n);
    const lpBrut = 'Minimize' + NL + ' obj: ' + objTxt.join(' ').replace(/^\+ /, '') + NL + 'Subject To' + NL + L.join(NL) + NL + 'Bounds' + NL + gen.map(g => ' 0 <= ' + g).join(NL) + NL + 'Binary' + NL + ' ' + bin.join(NL + ' ') + NL + 'End' + NL;
    const lp = lpBrut.split(NL).map(l => { if (l.length < 200) return l; const out = []; let cur = ''; l.split(/(?= [+-] )/).forEach(t => { if (cur.length + t.length > 200) { out.push(cur); cur = ' ' + t.trim(); } else cur += t; }); out.push(cur); return out.join(NL); }).join(NL);
    return { lp, xv, DEMI, taille: { variables: xv.length, auxiliaires: gen.length, contraintes: L.length }, toleres: toleres + toleresRepos, tolereEx, log };
  }

  /* Lit le résultat de HiGHS. */
  function lire(E, mod, r, dt) {
    const aff = {}, trous = [];
    const col = n => r.Columns && r.Columns[n] && r.Columns[n].Primal > 0.5;
    mod.xv.forEach(v => { if (col(v.n)) (aff[v.c.dk] = aff[v.c.dk] || {})[v.c.pid] = v.d; });
    E.demande.forEach((c, ci) => { if (col('t' + ci)) trous.push({ dk: c.dk, pid: c.pid }); });
    const forces = mod.xv.filter(v => v.force && col(v.n)).length;
    const ok = r.Status === 'Optimal' || r.Status === 'Time limit reached' || r.Status === 'Interrupted by user';
    return { statut: r.Status, objectif: ok && isFinite(r.ObjectiveValue) ? r.ObjectiveValue : Infinity, secondes: dt, affectations: aff, trous, forces,
      demi: mod.DEMI.filter(o => col(o.h)).map(o => ({ dk: o.dk, pid: o.pid, doc: o.doc, heures: o.heures, second: (aff[o.dk] || {})[o.pid] })) };
  }

  /* Solution de départ à partir d'un planning existant (celui du moteur) : seules les cases à pourvoir sont reprises. */
  function depuisPlanning(E, planning, demiExistantes) {
    const aff = {};
    E.demande.forEach(c => { const d = (planning[c.dk] || {})[c.pid]; if (d != null) (aff[c.dk] = aff[c.dk] || {})[c.pid] = d; });
    return { objectif: Infinity, affectations: aff, trous: [], forces: 0, demi: demiExistantes || [] };
  }

  /* Amélioration par fenêtres glissantes : libère `taille` jours tous les `pas` jours, garde chaque amélioration.
     o : { highs, depart (solution), dureeS, taille, pas, limiteS, progres(fn), arreter(fn → bool), maintenant(fn) } */
  function ameliorer(E, o) {
    const maintenant = o.maintenant || (() => Date.now()); const t0 = maintenant();
    const duree = (o.dureeS || 1800) * 1000, taille = o.taille || 7, pas = o.pas || 4, limite = o.limiteS || 150;
    const jours = E.jours.slice().sort(); const fen = []; for (let i = 0; i < jours.length; i += pas) fen.push([jours[i], jours[Math.min(jours.length - 1, i + taille - 1)]]);
    let best = Object.assign({}, o.depart), passage = 0, essais = 0, gains = 0;
    if (typeof best.objectif !== 'number' || isNaN(best.objectif)) best.objectif = Infinity;   // JSON change Infinity en null : le départ doit toujours céder à la 1re solution
    const reste = () => duree - (maintenant() - t0);
    while (reste() > 5000 && !(o.arreter && o.arreter())) {
      passage++; let gain = 0;
      for (const [deb, fin] of fen) {
        if (reste() <= 5000 || (o.arreter && o.arreter())) break;
        const mod = construire(E, { init: best, deb, fin, poids: o.poids });
        const t1 = maintenant(); let r;
        try { r = o.highs.solve(mod.lp, Object.assign({ time_limit: Math.max(10, Math.min(limite, Math.floor(reste() / 1000) - 2)), mip_rel_gap: 0.002 }, o.options || {})); }
        catch (e) { if (o.progres) o.progres({ type: 'erreur', fenetre: [deb, fin], message: String(e && e.message || e).slice(0, 200) }); continue; }
        const s = lire(E, mod, r, (maintenant() - t1) / 1000); essais++;
        if (isFinite(s.objectif) && (!isFinite(best.objectif) || s.objectif < best.objectif - 0.5)) { gain += isFinite(best.objectif) ? best.objectif - s.objectif : 1; gains++; best = s; }
        // postes vides « réels » : une case que le départ tenait déjà reste tenue dans le brouillon (affectation du départ gardée)
        const A0 = (o.depart && o.depart.affectations) || {}; const trousReels = (best.trous || []).filter(t => (A0[t.dk] || {})[t.pid] == null).length;
        if (o.progres) o.progres({ type: 'fenetre', passage, fenetre: [deb, fin], objectif: best.objectif, trous: trousReels, aReprendre: (best.trous || []).length - trousReels, forces: best.forces, demi: (best.demi || []).length, essais, gains, toleres: mod.toleres, statut: r.Status, ecoule: (maintenant() - t0) / 1000, total: duree / 1000, meilleur: best });
      }
      if (gain < 1) break;
    }
    return best;
  }

  // ── Règles v8 (retrouvées dans les conversations) ───────────────────────────────────────────────────────────────────────
  function reglesV8(X) {
    const { E, xv, parDoc, C, addObj, gen, bin, somme, isoWeek, dayN, nomDe, NOMS, I, mi, M, enPeriode } = X;
    const W = Object.assign({ chaineCasse: 3000, exception: 40, chaine: 300, chefAdmin: 100, we2: 80, weRepet: 200, weConsec: 80, doubSem: 20, memePoste: 15, vendConsec: 40, typesNuit: 10, DE: 40, adminSem: 50 }, X.W8 || {});
    let k = 0; const aux = (poids, binaire) => { const n = 'v8_' + (k++); (binaire ? bin : gen).push(n); if (poids) addObj(n, poids); return n; };
    const role = d => ((E.docs.find(x => x.id === d) || {}).role || '');
    const estPH = d => /^PH/.test(role(d)), estAsst = d => /^Assistant/.test(role(d));
    const special = d => !!((NOMS.find(r => r.local_id === d) || {}).special_case);
    const CHEFS = ['DEGESVES', 'STECKX', 'BUSCH', 'VAN BRUSSEL'];
    const fixeDe = (d, dk) => E.autour.filter(a => a.doc === d && a.dk === dk).map(a => a.pid);
    const parCaseJour = {}; xv.forEach(v => { const key = v.c.dk + '|' + v.c.pid; (parCaseJour[key] = parCaseJour[key] || []).push(v); });
    const souh = new Set(E.souhaits.map(([ci, d]) => ci + '|' + d));
    // 1. chaînage jour → nuit
    const PAIRES = [['coord', 'coord-n'], ['a', 'satmu-n'], ['b', 'smur-n']];
    [...new Set(E.demande.map(c => c.dk))].forEach(dk => { if (E.dow[dk] === 0 || E.dow[dk] === 6 || E.ferie.includes(dk)) return;
      PAIRES.forEach(([pj, pn]) => { const J = parCaseJour[dk + '|' + pj] || [], N = parCaseJour[dk + '|' + pn] || []; if (!J.length || !N.length) return;
        const exc = [];
        N.forEach(vn => { const d = vn.d; let e = null;
          if (CHEFS.includes(nomDe(d))) { const adm = (parCaseJour[dk + '|admin'] || []).find(w => w.d === d); const admFixe = fixeDe(d, dk).includes('admin');
            if (adm || admFixe) { e = aux(W.exception, false); C(e + ' - ' + vn.n, '<= 0'); if (adm && !admFixe) C(e + ' - ' + adm.n, '<= 0'); } }
          else if (pn === 'smur-n' && estAsst(d)) { e = aux(W.exception, false); C(e + ' - ' + vn.n, '<= 0'); }
          else if (souh.has(vn.ci + '|' + d)) { e = aux(0, false); C(e + ' - ' + vn.n, '<= 0'); }
          if (e) exc.push(e); });
        const br = aux(W.chaineCasse, false);
        J.forEach(vj => { const vn = N.find(w => w.d === vj.d); C(vj.n + (vn ? ' - ' + vn.n : '') + (exc.length ? ' - ' + exc.join(' - ') : '') + ' - ' + br, '<= 0'); });
        if (exc.length > 1) C(exc.join(' + '), '<= 1'); }); });
    // 2. chefs « spécialistes admin »
    xv.filter(v => VN.includes(v.c.pid) && CHEFS.includes(nomDe(v.d)) && E.dow[v.c.dk] >= 1 && E.dow[v.c.dk] <= 5).forEach(v => {
      if (nomDe(v.d) === 'DEGESVES' && E.dow[v.c.dk] === 3) return;
      const jour = PAIRES.find(([, n]) => n === v.c.pid)[0];
      const cands = ['admin', jour].map(p => (parCaseJour[v.c.dk + '|' + p] || []).find(w => w.d === v.d)).filter(Boolean);
      if (fixeDe(v.d, v.c.dk).some(p => p === 'admin' || p === jour)) return;
      const z = aux(W.chefAdmin, false); C(v.n + (cands.length ? ' - ' + somme(cands) : '') + ' - ' + z, '<= 0'); });
    // 3. week-ends des PH (doublure = demi-garde) et WE consécutifs
    const weekendDe = dk => { const t = new Date(dk + 'T12:00:00Z'); t.setUTCDate(t.getUTCDate() - ((t.getUTCDay() + 6) % 7)); return t.toISOString().slice(0, 10); };
    const WEP = WEQ.concat(['we-u3-sat', 'we-u3-sun', 'we-e', 'we-doublure']);
    Object.entries(parDoc).forEach(([dS, vs]) => { const d = +dS; if (!estPH(d)) return;
      const we = vs.filter(v => WEP.includes(v.c.pid)); if (!we.length) return;
      const fx = E.autour.filter(a => a.doc === d && WEP.includes(a.pid));
      const deux = []; const poids = p => p === 'we-doublure' ? 0.5 : 1, terme = x => x.map(v => (poids(v.c.pid) === 1 ? '' : '0.5 ') + v.n).join(' + ');
      M.forEach(m => { const x = we.filter(v => v.c.m === m); const f = fx.filter(a => mi(a.dk) === m).reduce((s, a) => s + poids(a.pid), 0); if (!x.length) return;
        // [17/11] tolérance du départ : si le planning de départ dépasse déjà 3,5 WE ce mois-ci (ex. T2 sans assistants : 5 WE),
        // la ligne « z = 1 dès 2 WE » doit rester satisfaisable avec z = 1
        const ti = X.tient ? x.filter(X.tient).reduce((s, v) => s + poids(v.c.pid), 0) : 0;
        C(terme(x), '<= ' + Math.max(0, 2 - f)); const z = aux(W.we2, true); C(terme(x) + ' - 2 ' + z, '<= ' + Math.max(1.5 - f, ti - 2)); deux.push(z); });
      if (deux.length > 1) { const r = aux(W.weRepet, false); C(deux.join(' + ') + ' - ' + r, '<= 1'); }
      const parWe = {}; we.forEach(v => (parWe[weekendDe(v.c.dk)] = parWe[weekendDe(v.c.dk)] || []).push(v));
      const fixWe = new Set(fx.map(a => weekendDe(a.dk)));
      [...new Set(Object.keys(parWe).concat([...fixWe]))].sort().forEach(w => { const t = new Date(w + 'T12:00:00Z'); t.setUTCDate(t.getUTCDate() + 7); const w2 = t.toISOString().slice(0, 10);
        const a = parWe[w] || [], b = parWe[w2] || []; const fa = fixWe.has(w) ? 1 : 0, fb = fixWe.has(w2) ? 1 : 0;
        if ((a.length || fa) && (b.length || fb) && (a.length || b.length)) { const z = aux(W.weConsec, false); C((a.concat(b).length ? somme(a.concat(b)) + ' - ' : '') + z, '<= ' + Math.max(0, 1 - fa - fb)); } });
    });
    // 4. doublures de jour : 2 par semaine
    Object.entries(parDoc).forEach(([, vs]) => { const sw = {}; vs.filter(v => DOUB.includes(v.c.pid)).forEach(v => (sw[isoWeek(v.c.dk)] = sw[isoWeek(v.c.dk)] || []).push(v));
      Object.values(sw).forEach(x => { if (x.length > 2) { const z = aux(W.doubSem, false); C(somme(x) + ' - ' + z, '<= 2'); } }); });
    // 5. même poste deux jours de suite
    const SUITE = ['smur-j', 'satmu-j', 'doubl-u-ad', 'doubl-u-bc'], U3 = ['u3-1', 'u3-2', 'u3-3', 'u3-4', 'u3-5'];
    Object.entries(parDoc).forEach(([dS, vs]) => { const d = +dS; const posts = SUITE.concat(estPH(d) && nomDe(d) !== 'FOAMKOM' ? U3 : []);
      const pj = {}; vs.filter(v => posts.includes(v.c.pid)).forEach(v => { const key = v.c.pid.startsWith('u3') ? 'u3' : v.c.pid; (pj[key + '|' + dayN(v.c.dk)] = pj[key + '|' + dayN(v.c.dk)] || []).push(v); });
      Object.keys(pj).forEach(kk => { const [p, j] = kk.split('|'); const s = pj[p + '|' + (+j + 1)]; if (s) { const z = aux(W.memePoste, false); C(somme(pj[kk].concat(s)) + ' - ' + z, '<= 1'); } }); });
    // 6. pas deux vendredis de garde d'affilée
    const VG = ['coord-n', 'smur-n', 'satmu-n', 'pm14', 'pm16', 'n16'];
    Object.entries(parDoc).forEach(([dS, vs]) => { const d = +dS; const pv = {}; vs.filter(v => E.dow[v.c.dk] === 5 && VG.includes(v.c.pid)).forEach(v => (pv[dayN(v.c.dk)] = pv[dayN(v.c.dk)] || []).push(v));
      const fixV = new Set(E.autour.filter(a => a.doc === d && VG.includes(a.pid) && new Date(a.dk + 'T12:00:00Z').getUTCDay() === 5).map(a => dayN(a.dk)));
      Object.keys(pv).map(Number).forEach(j => { const s = pv[j + 7] || []; if (s.length) { const z = aux(W.vendConsec, false); C(somme(pv[j].concat(s)) + ' - ' + z, '<= 1'); }
        if (fixV.has(j - 7)) { const z = aux(W.vendConsec, false); C(somme(pv[j]) + ' - ' + z, '<= 0'); } }); });
    // 7. 14-22 et 16-00
    Object.entries(parDoc).forEach(([dS, vs]) => { const d = +dS; const pm = vs.filter(v => v.c.pid === 'pm14');
      if (/Généraliste/.test(role(d))) { const sw = {}; pm.forEach(v => (sw[isoWeek(v.c.dk)] = sw[isoWeek(v.c.dk)] || []).push(v)); Object.values(sw).forEach(x => { if (x.length > 1) C(somme(x), '<= 1'); }); }
      if (estAsst(d)) M.forEach(m => { const x = pm.filter(v => v.c.m === m); if (x.length > 1) C(somme(x), '<= 1'); });
      const cap16 = nomDe(d) === 'BIÉMAR' ? 1 : 3; M.forEach(m => { const x = vs.filter(v => v.c.pid === 'pm16' && v.c.m === m); const f = E.autour.filter(a => a.doc === d && a.pid === 'pm16' && mi(a.dk) === m).length; if (x.length > cap16 - f) C(somme(x), '<= ' + Math.max(0, cap16 - f)); }); });
    // 8. enchaînements interdits
    Object.entries(parDoc).forEach(([dS, vs]) => { const d = +dS; const interdits = estAsst(d) ? [['b', 'smur-n']] : nomDe(d) === 'BIÉMAR' ? [['a', 'satmu-n'], ['b', 'smur-n']] : [];
      interdits.forEach(([p, q]) => vs.filter(v => v.c.pid === p).forEach(v => { const w = vs.find(u => u.c.dk === v.c.dk && u.c.pid === q); if (w) C(v.n + ' + ' + w.n, '<= 1'); })); });
    // 9. types de nuits équilibrés
    Object.entries(parDoc).forEach(([, vs]) => { const types = VN.filter(p => vs.some(v => v.c.pid === p)); if (types.length < 2) return;
      for (let i = 0; i < types.length; i++) for (let j = 0; j < types.length; j++) { if (i === j) continue;
        const a = vs.filter(v => v.c.pid === types[i]), b = vs.filter(v => v.c.pid === types[j]); const z = aux(W.typesNuit, false);
        C(somme(a) + ' - ' + b.map(v => v.n).join(' - ') + ' - ' + z, '<= 2'); } });
    // 10. pas de doublure WE (D) et de poste E (16-00 / WE-E) le même mois
    Object.entries(parDoc).forEach(([dS, vs]) => { const d = +dS; M.forEach(m => {
      const EP = ['pm16', 'we-e'], fx = E.fixes.filter(f => f.doc === d && mi(f.dk) === m);
      const dd = vs.filter(v => v.c.pid === 'we-doublure' && v.c.m === m), ee = vs.filter(v => EP.includes(v.c.pid) && v.c.m === m);
      const dF = fx.some(f => f.pid === 'we-doublure'), eF = fx.some(f => EP.includes(f.pid));
      if ((!dd.length && !dF) || (!ee.length && !eF)) return;
      const a = dF ? null : aux(0, true), b = eF ? null : aux(0, true);
      if (a) C(somme(dd) + ' - ' + dd.length + ' ' + a, '<= 0'); if (b) C(somme(ee) + ' - ' + ee.length + ' ' + b, '<= 0');
      const z = aux(W.DE, false); const t = [a, b].filter(Boolean); C(t.join(' + ') + ' - ' + z, '<= ' + (t.length - 1)); }); });
    // 11. cas particuliers
    Object.entries(parDoc).forEach(([dS, vs]) => { const d = +dS;
      if (special(d) || ['MILET', 'CHARPENTIER'].includes(nomDe(d))) { M.forEach(m => { const x = vs.filter(v => VN.concat(['n16']).includes(v.c.pid) && v.c.m === m); if (x.length > 1) C(somme(x), '<= 1'); });
        const w = vs.filter(v => WEQ.includes(v.c.pid)); const f = E.autour.filter(a => a.doc === d && WEQ.includes(a.pid) && enPeriode(a.dk)).length; if (w.length > Math.max(0, 1 - f)) C(somme(w), '<= ' + Math.max(0, 1 - f)); }
      if (nomDe(d) === 'WINKIN') vs.filter(v => E.dow[v.c.dk] === 0 && ['we-coord', 'we-smur-sun', 'we-satmu'].includes(v.c.pid)).forEach(v => C(v.n, '= 0'));
      if (nomDe(d) === 'SORCE') vs.filter(v => E.dow[v.c.dk] === 0 && v.c.pid.startsWith('we-')).forEach(v => C(v.n, '= 0')); });
    // 12. admin hebdomadaire
    Object.entries(parDoc).forEach(([dS, vs]) => { const d = +dS; if (!['DEGESVES', 'STECKX', 'BUSCH'].includes(nomDe(d))) return;
      const sw = {}; vs.filter(v => v.c.pid === 'admin').forEach(v => (sw[isoWeek(v.c.dk)] = sw[isoWeek(v.c.dk)] || []).push(v));
      Object.entries(sw).forEach(([w, x]) => { if (E.autour.some(a => a.doc === d && a.pid === 'admin' && isoWeek(a.dk) == w)) return; const u = aux(W.adminSem, false); C(somme(x) + ' + ' + u, '>= 1'); }); });
  }

  // ── Règles v10 (règles du moteur + proportionnalité) ─────────────────────────────────────────────────────────────────
  function definitionsV10(E, NOMS, mi, M) {
    const D = id => E.docs.find(x => x.id === id) || { regles: [], parMois: M.map(() => ({})) };
    const N = id => NOMS.find(r => r.local_id === id) || {};
    const GARDE = VN.concat(WEQ);
    const joursGarde = M.map(() => new Set());
    E.demande.forEach(c => { if (GARDE.includes(c.pid)) joursGarde[c.m].add(c.dk); });
    E.fixes.forEach(f => { if (GARDE.includes(f.pid) && mi(f.dk) >= 0) joursGarde[mi(f.dk)].add(f.dk); });
    const dispo = {}; const vide = () => M.map(() => new Set());
    const ajoute = (ci, d) => { const c = E.demande[ci]; if (!GARDE.includes(c.pid)) return; ((dispo[d] = dispo[d] || vide())[c.m]).add(c.dk); };
    E.elig.forEach(([ci, d]) => ajoute(ci, d)); E.forcables.forEach(([ci, d]) => ajoute(ci, d)); (E.chainables || []).forEach(([ci, d]) => ajoute(ci, d));
    E.fixes.forEach(f => { if (GARDE.includes(f.pid) && mi(f.dk) >= 0) ((dispo[f.doc] = dispo[f.doc] || vide())[mi(f.dk)]).add(f.dk); });
    const tauxDispo = (d, m) => joursGarde[m].size ? ((dispo[d] || [])[m] || new Set()).size / joursGarde[m].size : 0;
    const regle = (d, t) => (D(d).regles || []).filter(r => r.type === t);
    const delta = d => regle(d, 'garde_quota_delta').reduce((a, r) => a + (+r.delta || +r.count || 1), 0);
    const phGarde = E.docs.filter(x => (x.role === 'PH Urgences' || x.role === 'PH SMUR') && !N(x.id).special_case && !/^TEST$/i.test(N(x.id).lastname || '') && M.some(m => tauxDispo(x.id, m) > 0)).map(x => x.id);
    const pmD = (d, m) => (D(d).parMois || [])[m] || {};
    const receveur = (d, m) => tauxDispo(d, m) >= 0.85 && (pmD(d, m).wd || 0) + (pmD(d, m).we || 0) >= 3 && !regle(d, 'max_gardes_per_month').length;
    const seuilDonneur = d => 4 - delta(d);
    const capacite = d => (D(d).h || 0) * M.reduce((a, m) => a + tauxDispo(d, m), 0) / M.length;
    const libreETP = d => !delta(d) && !regle(d, 'max_gardes_per_month').length;
    const pairesETP = []; phGarde.filter(libreETP).forEach(a => phGarde.filter(libreETP).forEach(b => { if (a !== b && capacite(b) > 0 && capacite(a) >= 1.25 * capacite(b) && (D(a).h || 0) > (D(b).h || 0)) pairesETP.push([a, b]); }));
    const BIEMAR = (NOMS.find(r => (r.lastname || '').toUpperCase() === 'BIÉMAR') || {}).local_id;
    const prio = []; E.docs.forEach(x => (x.regles || []).filter(r => r.type === 'priority_on_post').forEach(r => prio.push({ d: x.id, posts: r.posts || [], lim: r.monthlyLimit != null ? +r.monthlyLimit : null })));
    return { GARDE, tauxDispo, phGarde, receveur, seuilDonneur, pairesETP, BIEMAR, prio, estAsst: d => /^Assistant/.test(D(d).role || ''), estPH: d => /^PH/.test(D(d).role || '') };
  }
  function reglesV10(X) {
    const { E, parDoc, C, addObj, gen, bin, somme, NOMS, mi, M } = X;
    const W = Object.assign({ plancher: 150, etp: 15, liss: 20, biemar: 5, prio: 8, weFerie: 500 }, X.W10 || {});
    const R = definitionsV10(E, NOMS, mi, M);
    let k = 0; const aux = (poids, binaire) => { const n = 'v10_' + (k++); (binaire ? bin : gen).push(n); if (poids) addObj(n, poids); return n; };
    const fixesGarde = (d, m) => E.fixes.filter(f => f.doc === d && mi(f.dk) === m && R.GARDE.includes(f.pid)).length;
    const gardesDe = (d, m) => (parDoc[d] || []).filter(v => R.GARDE.includes(v.c.pid) && v.c.m === m);
    // 1. plancher des gardes PH
    M.forEach(m => { const rec = R.phGarde.filter(d => R.receveur(d, m)); if (!rec.length) return; const Lr = aux(0, true);
      rec.forEach(b => { const vs = gardesDe(b, m), f = fixesGarde(b, m); if (f >= 3 || vs.length + f < 3) return; const l = aux(0, true);
        C((vs.length ? somme(vs) + ' + ' : '') + '3 ' + l, '>= ' + (3 - f)); C(l + ' - ' + Lr, '<= 0'); });
      R.phGarde.forEach(a => { const vs = gardesDe(a, m), f = fixesGarde(a, m), s = R.seuilDonneur(a); if (!vs.length) return;
        const u = aux(0, true); C(somme(vs) + ' - 6 ' + u, '<= ' + (s - 1 - f)); const z = aux(W.plancher, false); C(u + ' + ' + Lr + ' - ' + z, '<= 1'); }); });
    // 2. proportionnalité au temps de travail
    const totalG = d => ({ vs: M.flatMap(m => gardesDe(d, m)), f: M.reduce((a, m) => a + fixesGarde(d, m), 0) });
    R.pairesETP.forEach(([a, b]) => { const A = totalG(a), B = totalG(b); if (!B.vs.length) return; const y = aux(W.etp, false);
      C(somme(B.vs) + (A.vs.length ? ' - ' + A.vs.map(v => v.n).join(' - ') : '') + ' - ' + y, '<= ' + (A.f - B.f)); });
    // 3. lissage mensuel des assistants (plafonds trimestriels au rythme du trimestre)
    const LISS = { 'smur-j': 4, 'doub-coord': 9, 'doub-smur': 15 };
    const posTrim = m => (+E.mois[m].slice(5, 7) - 1) % 3, rythme = (cap, m) => Math.ceil(cap * (posTrim(m) + 1) / 3);
    Object.entries(parDoc).forEach(([dS, vs]) => { const d = +dS; if (!R.estAsst(d)) return;
      Object.entries(LISS).forEach(([p, cap]) => { M.forEach(m => { if (posTrim(m) === 2) return; const cum = vs.filter(v => v.c.pid === p && v.c.m <= m && posTrim(v.c.m) <= posTrim(m)); if (cum.length <= rythme(cap, m)) return;
        const e = aux(W.liss, false); C(somme(cum) + ' - ' + e, '<= ' + rythme(cap, m)); }); }); });
    // 4. BIÉMAR : (A+B+C+D) = 2 × (U3 + 16-00)
    if (R.BIEMAR != null && parDoc[R.BIEMAR]) { const vs = parDoc[R.BIEMAR]; const jour = vs.filter(v => ['a', 'b', 'c', 'd'].includes(v.c.pid)), u3 = vs.filter(v => /^u3-/.test(v.c.pid) || v.c.pid === 'pm16');
      if (jour.length || u3.length) { const p = aux(W.biemar, false), q = aux(W.biemar, false); const t = jour.map(v => '+ ' + v.n).concat(u3.map(v => '- 2 ' + v.n)).join(' ').replace(/^\+ /, ''); C(t + ' - ' + p + ' + ' + q, '= 0'); } }
    // 5. priorités de poste
    R.prio.forEach(({ d, posts, lim }) => { const vs = (parDoc[d] || []).filter(v => posts.includes(v.c.pid) && !v.force); if (!vs.length) return;
      if (lim == null) { vs.forEach(v => addObj(v.n, -W.prio)); return; }
      M.forEach(m => { const x = vs.filter(v => v.c.m === m); if (!x.length) return; const kk = aux(-W.prio, false); C(kk + ' - ' + x.map(v => v.n).join(' - '), '<= 0'); C(kk, '<= ' + Math.min(lim, x.length)); }); });
    // 6. WE + férié
    const FER = new Set(E.ferie);
    Object.entries(parDoc).forEach(([dS, vs]) => { const d = +dS; if (!R.estPH(d)) return;
      M.forEach(m => { const x = vs.filter(v => v.c.m === m && (WEQ.includes(v.c.pid) || v.c.pid === 'we-doublure' || (FER.has(v.c.dk) && R.GARDE.concat(['pm16', 'n16']).includes(v.c.pid))));
        const pw = p => p === 'we-doublure' ? 0.5 : 1;
        const f = E.fixes.filter(a => a.doc === d && mi(a.dk) === m && (WEQ.includes(a.pid) || a.pid === 'we-doublure' || FER.has(a.dk))).reduce((t, a) => t + pw(a.pid), 0);
        if (x.reduce((t, v) => t + pw(v.c.pid), 0) + f <= 2) return; const e = aux(W.weFerie, false); C(x.map(v => (pw(v.c.pid) === 1 ? '' : '0.5 ') + v.n).join(' + ') + ' - ' + e, '<= ' + Math.max(0, 2 - f)); }); });
    // 7. max_gardes_per_month (dure)
    E.docs.forEach(Dc => (Dc.regles || []).filter(r => r.type === 'max_gardes_per_month').forEach(r => M.forEach(m => { const G7 = R.GARDE.concat(['n16']);
      const x = (parDoc[Dc.id] || []).filter(v => v.c.m === m && G7.includes(v.c.pid)); const f = E.fixes.filter(a => a.doc === Dc.id && mi(a.dk) === m && G7.includes(a.pid)).length;
      if (x.length) C(somme(x), '<= ' + Math.max(0, (+r.count || 1) - f)); })));
  }

  // ── Demi-garde de WE de jour (règle de fiche we_half_day_month) ───────────────────────────────────────────────────────
  function demiGarde(X) {
    const { E, W, parDoc, parCase, C, addObj, gen, bin, I, dayN, nxt, HX, init, deb, fin } = X;
    const NOMS = E.noms || [], IND = E.indispos || [];
    const WEC = WEQ.concat(['we-doublure']), wPoids = p => (p === 'we-doublure' ? 0.5 : 1);
    const I0 = (init && init.demi) || []; const enFenetre = dk => !deb || (dk >= deb && dk <= fin);
    const sortie = [];
    E.docs.forEach(D => { const regles = (D.regles || []).filter(r => r && r.type === 'we_half_day_month' && r.active !== false); if (!regles.length) return;
      const R = NOMS.find(x => x.local_id === D.id) || {}; const ep = R.extra_profile || {};
      const indispoJour = dk => { if (R.contract_start && dk < R.contract_start) return true; if (R.contract_end && dk > R.contract_end) return true;
        const dow = new Date(dk + 'T12:00:00Z').getUTCDay(); if ((ep.unavailDow || []).some(u => u.dow === dow)) return true;
        return IND.some(i => i.docId === D.id && dk >= i.start && dk <= i.end && i.type !== 'pref' && i.type !== 'unavail_post'); };
      const indispoPoste = (dk, pid) => IND.some(i => i.docId === D.id && i.type === 'unavail_post' && dk >= i.start && dk <= i.end && (i.posteId === pid || /^section:(we|garde)/.test(String(i.posteId || ''))));
      const fix = E.autour.filter(a => a.doc == D.id); const vsB = parDoc[D.id] || [];
      regles.forEach(r => { const P = (r.posts || []).filter(p => WEQ.includes(p)); const N = Math.max(0, r.count != null ? +r.count : 1); const hh = (+r.hours > 0 && +r.hours < 24) ? +r.hours : 12;
        const hs = [];
        E.demande.forEach((c, ci) => { if (!P.includes(c.pid)) return; const dk = c.dk;
          if (indispoJour(dk) || indispoPoste(dk, c.pid)) return;
          if (fix.some(a => a.dk === dk || a.dk === nxt(dk, 1))) return;
          if (fix.some(a => a.dk === nxt(dk, -1) && I(a.pid).repos)) return;
          if (fix.some(a => I(a.pid).garde && Math.abs(dayN(a.dk) - dayN(dk)) <= 2)) return;
          if (fix.some(a => WEC.includes(a.pid) && Math.abs(dayN(a.dk) - dayN(dk)) >= 5 && Math.abs(dayN(a.dk) - dayN(dk)) <= 9)) return;
          if (!(parCase[ci] || []).some(v => v.d !== D.id)) return;
          const h = 'h' + D.id + '_' + ci; bin.push(h); hs.push({ h, ci, c, hh });
          if (!enFenetre(dk)) C(h, '= ' + (I0.some(x => x.dk === dk && x.pid === c.pid && x.doc === D.id) ? 1 : 0)); });
        X.M.forEach(m => { const x = hs.filter(o => o.c.m === m); if (!x.length) return; const u = 'udemi' + D.id + '_' + m; gen.push(u); addObj(u, W.demi);
          C(x.map(o => o.h).join(' + '), '<= ' + N); C(x.map(o => o.h).join(' + ') + ' + ' + u, '>= ' + N); });
        hs.forEach(o => { const dk = o.c.dk;
          (parCase[o.ci] || []).filter(v => v.d === D.id).forEach(v => C(v.n + ' + ' + o.h, '<= 1'));
          vsB.filter(v => v.c.dk === dk || v.c.dk === nxt(dk, 1)).forEach(v => C(v.n + ' + ' + o.h, '<= 1'));
          vsB.filter(v => v.c.dk === nxt(dk, -1) && I(v.c.pid).repos).forEach(v => C(v.n + ' + ' + o.h, '<= 1'));
          if (E.dow[dk] === 0) vsB.filter(v => v.c.dk === nxt(dk, -2) && I(v.c.pid).reposDim).forEach(v => C(v.n + ' + ' + o.h, '<= 1'));
          vsB.filter(v => I(v.c.pid).garde && v.c.dk !== dk && Math.abs(dayN(v.c.dk) - dayN(dk)) <= 2).forEach(v => C(v.n + ' + ' + o.h, '<= 1'));
          vsB.filter(v => /^we-/.test(v.c.pid) && Math.abs(dayN(v.c.dk) - dayN(dk)) === 1).forEach(v => C(v.n + ' + ' + o.h, '<= 1'));
          vsB.filter(v => WEC.includes(v.c.pid) && Math.abs(dayN(v.c.dk) - dayN(dk)) >= 5 && Math.abs(dayN(v.c.dk) - dayN(dk)) <= 9).forEach(v => C(v.n + ' + ' + o.h, '<= 1'));
          hs.filter(q => q !== o && Math.abs(dayN(q.c.dk) - dayN(dk)) >= 1 && Math.abs(dayN(q.c.dk) - dayN(dk)) <= 9).forEach(q => { if (q.ci > o.ci) C(q.h + ' + ' + o.h, '<= 1'); });
          hs.filter(q => q !== o && q.c.dk === dk && q.ci > o.ci).forEach(q => C(q.h + ' + ' + o.h, '<= 1'));
          (parCase[o.ci] || []).filter(v => v.d !== D.id).forEach(v => { const y = 'y' + o.h.slice(1) + '_' + v.d; gen.push(y);
            C(y + ' - ' + v.n, '<= 0'); C(y + ' - ' + o.h, '<= 0'); C(v.n + ' + ' + o.h + ' - ' + y, '<= 1');
            const m = o.c.m, autres = (parDoc[v.d] || []).filter(w => WEC.includes(w.c.pid) && w.c.m === m);
            const fixeCharge = E.autour.filter(a => a.doc == v.d && WEC.includes(a.pid) && X.mi(a.dk) === m).reduce((s, a) => s + wPoids(a.pid), 0);
            C(autres.map(w => wPoids(w.c.pid) + ' ' + w.n).join(' + ') + ' + 10 ' + y, '<= ' + (12 - fixeCharge));
            (HX[v.d] = HX[v.d] || []).push('- ' + o.hh + ' ' + y); });
          (HX[D.id] = HX[D.id] || []).push('+ ' + o.hh + ' ' + o.h);
          sortie.push({ h: o.h, dk, pid: o.c.pid, doc: D.id, ci: o.ci, heures: o.hh }); });
      });
    });
    return sortie;
  }

  return { construire, lire, depuisPlanning, ameliorer, POIDS };
}));
