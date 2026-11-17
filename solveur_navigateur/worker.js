/* Worker du solveur (gestionnaire, Citadelle) : charge HiGHS (WebAssembly) et le modèle, améliore le planning par fenêtres
   et renvoie la progression. Messages reçus : { type:'lancer', E, depart, dureeS, taille, pas, limiteS }.
   Messages envoyés : { type:'pret' } ; { type:'progres', … , meilleur? } ; { type:'fin', meilleur } ; { type:'erreur', message }.
   « Arrêter » se fait depuis la page en terminant le worker : la page garde la dernière meilleure solution reçue. */
'use strict';
importScripts('highs.js', 'modele.js');
let highsPromesse = null;
const charger = () => highsPromesse || (highsPromesse = Module({ locateFile: f => f }));
self.onmessage = async ev => {
  const m = ev.data || {};
  if (m.type !== 'lancer') return;
  try {
    const highs = await charger();
    self.postMessage({ type: 'pret' });
    let dernierObjectif = Infinity;
    const meilleur = SolveurModele.ameliorer(m.E, {
      highs, depart: m.depart, dureeS: m.dureeS, taille: m.taille, pas: m.pas, limiteS: m.limiteS,
      progres: p => {
        const msg = Object.assign({}, p); delete msg.meilleur;
        if (p.meilleur && p.objectif < dernierObjectif - 0.5) { dernierObjectif = p.objectif; msg.meilleur = p.meilleur; }   // la solution n'est envoyée que si elle s'améliore
        self.postMessage(Object.assign({}, msg, { type: 'progres', etape: p.type }));   // p.type (« fenetre », « erreur ») ne doit pas écraser le type du message
      }
    });
    self.postMessage({ type: 'fin', meilleur });
  } catch (e) {
    self.postMessage({ type: 'erreur', message: String((e && e.message) || e).slice(0, 400) });
  }
};
