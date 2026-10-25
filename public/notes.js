/**
 * Surligner un passage, le commenter, en faire une issue GitHub.
 *
 * Le site est statique : rien n'est envoyé nulle part tant que le lecteur ne
 * clique pas sur « Ouvrir une issue ». Les notes sont gardées dans le
 * navigateur (localStorage), page par page ; l'issue s'ouvre sur GitHub,
 * pré-remplie avec le passage cité (les formules en TeX), le lien vers
 * l'endroit exact et le commentaire, et c'est le lecteur qui la publie.
 *
 * Le surlignage passe par l'API CSS Custom Highlight, qui colore des
 * intervalles de texte sans toucher au DOM : un passage peut donc traverser
 * une formule KaTeX sans la casser. Les navigateurs qui ne l'ont pas gardent
 * la liste des notes, sans la couleur.
 */
(function () {
  'use strict';

  var cfg = window.MA_NOTES || {};
  var article = document.querySelector('.ltx_document');
  if (!article || !cfg.repo) return;

  var KEY = 'ma-notes:' + location.pathname;
  var hasHighlight = typeof CSS !== 'undefined' && CSS.highlights && typeof Highlight !== 'undefined';

  // ---------------------------------------------------------------------
  // Le texte visible de l'article, à plat, avec la position de chaque nœud.
  // Le MathML caché que KaTeX place à côté de chaque formule est ignoré :
  // sans quoi chaque formule compterait deux fois.

  function textNodes() {
    var out = [];
    var walker = document.createTreeWalker(article, NodeFilter.SHOW_TEXT, {
      acceptNode: function (n) {
        var p = n.parentElement;
        if (!p || p.closest('.katex-mathml, .ma-ui')) return NodeFilter.FILTER_REJECT;
        return NodeFilter.FILTER_ACCEPT;
      },
    });
    var pos = 0;
    for (var n = walker.nextNode(); n; n = walker.nextNode()) {
      out.push({ node: n, start: pos });
      pos += n.data.length;
    }
    return out;
  }

  function flatText(nodes) {
    return nodes.map(function (x) { return x.node.data; }).join('');
  }

  /** Positions de début et de fin d'une sélection dans le texte à plat. */
  function offsetsOf(range, nodes) {
    var start = -1;
    var end = -1;
    for (var i = 0; i < nodes.length; i++) {
      var x = nodes[i];
      if (!range.intersectsNode(x.node)) continue;
      var s = x.node === range.startContainer ? range.startOffset : 0;
      var e = x.node === range.endContainer ? range.endOffset : x.node.data.length;
      if (start < 0) start = x.start + s;
      end = x.start + e;
    }
    return start < 0 || end <= start ? null : { start: start, end: end };
  }

  function rangeAt(nodes, start, end) {
    var r = document.createRange();
    var okStart = false;
    for (var i = 0; i < nodes.length; i++) {
      var x = nodes[i];
      var len = x.node.data.length;
      if (!okStart && start <= x.start + len) {
        r.setStart(x.node, start - x.start);
        okStart = true;
      }
      if (okStart && end <= x.start + len) {
        r.setEnd(x.node, end - x.start);
        return r;
      }
    }
    return null;
  }

  /** Le passage avec ses formules en TeX, pour l'issue. */
  function quoteWithTex(range) {
    var div = document.createElement('div');
    div.appendChild(range.cloneContents());
    div.querySelectorAll('.katex').forEach(function (k) {
      var tex = k.querySelector('annotation[encoding="application/x-tex"]');
      var display = k.parentElement && k.parentElement.classList.contains('katex-display');
      k.replaceWith(tex ? (display ? '\n$$' + tex.textContent.trim() + '$$\n' : '$' + tex.textContent.trim() + '$') : k.textContent);
    });
    div.querySelectorAll('.katex-mathml').forEach(function (k) { k.remove(); });
    return div.textContent.replace(/[ \t]+/g, ' ').replace(/\n{3,}/g, '\n\n').trim();
  }

  /** L'identifiant le plus proche avant le passage : énoncé, section, formule. */
  function anchorBefore(range) {
    var node = range.startContainer.nodeType === 1 ? range.startContainer : range.startContainer.parentElement;
    for (var el = node; el && el !== article; el = el.parentElement) {
      if (el.id) return el.id;
    }
    var ids = article.querySelectorAll('[id]');
    var best = '';
    ids.forEach(function (el) {
      if (el.compareDocumentPosition(node) & Node.DOCUMENT_POSITION_FOLLOWING) best = el.id;
    });
    return best;
  }

  /**
   * Le texte d'un élément, formules en TeX. `textContent` renverrait chaque
   * formule trois fois (le MathML caché, son annotation, puis le rendu) :
   * « modulo ppp » pour « modulo $p$ ».
   */
  function plainText(node) {
    var c = node.cloneNode(true);
    c.querySelectorAll('.katex').forEach(function (k) {
      var tex = k.querySelector('annotation[encoding="application/x-tex"]');
      k.replaceWith(tex ? '$' + tex.textContent.trim() + '$' : '');
    });
    return c.textContent.replace(/\s+/g, ' ').trim();
  }

  function labelOf(id) {
    var el = id && document.getElementById(id);
    if (!el) return '';
    if (el.matches('h2, h3')) return plainText(el);
    if (el.classList.contains('ltx_abstract')) return 'Résumé';
    var tag = el.querySelector('.ltx_tag');
    return tag ? plainText(tag) : '';
  }

  // ---------------------------------------------------------------------
  // Les notes gardées dans le navigateur.

  function load() {
    try { return JSON.parse(localStorage.getItem(KEY) || '[]'); } catch (e) { return []; }
  }
  function save(notes) {
    try { localStorage.setItem(KEY, JSON.stringify(notes)); } catch (e) { /* navigation privée */ }
  }

  /** Retrouve un passage : l'occurrence de son texte la plus proche de sa position d'origine. */
  function locate(note, nodes, text) {
    var best = -1;
    var from = 0;
    for (;;) {
      var i = text.indexOf(note.text, from);
      if (i < 0) break;
      if (best < 0 || Math.abs(i - note.start) < Math.abs(best - note.start)) best = i;
      from = i + 1;
    }
    return best < 0 ? null : rangeAt(nodes, best, best + note.text.length);
  }

  function paint() {
    if (!hasHighlight) return;
    var nodes = textNodes();
    var text = flatText(nodes);
    var ranges = load().map(function (n) { return locate(n, nodes, text); }).filter(Boolean);
    CSS.highlights.set('ma-note', new Highlight(...ranges));
  }

  // ---------------------------------------------------------------------
  // L'issue GitHub.

  function issueUrl(note) {
    var page = location.origin + location.pathname + (note.anchor ? '#' + note.anchor : '');
    var where = note.label ? note.label + ', ' : '';
    var title = '[' + (cfg.lecon || '') + '] ' + (note.comment ? note.comment.split('\n')[0] : 'Relecture : « ' + note.text.slice(0, 50) + ' »');
    var body =
      '**Document :** ' + (cfg.title || document.title) + '\n' +
      '**Passage :** ' + where + page + '\n' +
      (cfg.source ? '**Source :** `' + cfg.source + '`\n' : '') +
      '\n' + note.tex.split('\n').map(function (l) { return '> ' + l; }).join('\n') + '\n\n' +
      '**Commentaire :**\n\n' + (note.comment || '') + '\n';
    return 'https://github.com/' + cfg.repo + '/issues/new?title=' +
      encodeURIComponent(title.slice(0, 120)) + '&body=' + encodeURIComponent(body.slice(0, 6000));
  }

  /** Un passage court pour l'affichage : espaces de tête retirés, coupé à `max` caractères. */
  function excerpt(text, max) {
    var t = text.replace(/\s+/g, ' ').trim();
    return t.length > max ? t.slice(0, max) + '…' : t;
  }

  /**
   * Une seule issue pour toutes les notes de la page, dans l'ordre de lecture.
   * L'adresse d'une issue pré-remplie a une longueur limitée (environ 8 000
   * caractères une fois encodée) : les passages trop longs sont abrégés, et
   * si le tout dépasse encore, la fin est coupée avec un avertissement.
   */
  function summaryIssueUrl(notes) {
    var sorted = notes.slice().sort(function (a, b) { return a.start - b.start; });
    var base = location.origin + location.pathname;
    var title = '[' + (cfg.lecon || '') + '] Relecture : ' + sorted.length + ' remarque' + (sorted.length > 1 ? 's' : '') +
      ' sur « ' + (cfg.title || document.title) + ' »';
    var head =
      '**Document :** ' + (cfg.title || document.title) + '\n' +
      '**Page :** ' + base + '\n' +
      (cfg.source ? '**Source :** `' + cfg.source + '`\n' : '') + '\n';
    var parts = sorted.map(function (n, i) {
      var tex = n.tex.length > 500 ? n.tex.slice(0, 500) + '…' : n.tex;
      return '### ' + (i + 1) + '. ' + (n.label || 'Passage') + '\n' +
        base + (n.anchor ? '#' + n.anchor : '') + '\n\n' +
        tex.split('\n').map(function (l) { return '> ' + l; }).join('\n') + '\n\n' +
        (n.comment || '_(pas de commentaire)_') + '\n';
    });
    var body = head;
    var LIMIT = 5500;
    for (var i = 0; i < parts.length; i++) {
      if ((body + parts[i]).length > LIMIT) {
        body += '\n_… ' + (parts.length - i) + ' remarque(s) de plus, coupée(s) pour la longueur de l\'adresse : ouvrez-les une par une depuis la liste des notes._\n';
        break;
      }
      body += parts[i] + '\n';
    }
    return 'https://github.com/' + cfg.repo + '/issues/new?title=' +
      encodeURIComponent(title.slice(0, 120)) + '&body=' + encodeURIComponent(body);
  }

  // ---------------------------------------------------------------------
  // L'interface : un bouton près de la sélection, un panneau pour écrire,
  // et la liste des notes de la page.

  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text != null) e.textContent = text;
    return e;
  }

  var fab = el('button', 'ma-ui ma-fab', 'Commenter');
  fab.type = 'button';
  fab.hidden = true;
  document.body.appendChild(fab);

  var panel = el('div', 'ma-ui ma-panel');
  panel.hidden = true;
  panel.setAttribute('role', 'dialog');
  panel.setAttribute('aria-label', 'Commenter le passage');
  document.body.appendChild(panel);

  var listBtn = el('button', 'ma-ui ma-list-btn');
  listBtn.type = 'button';
  document.body.appendChild(listBtn);

  var pending = null;

  function currentSelection() {
    var sel = window.getSelection();
    if (!sel || sel.isCollapsed || !sel.rangeCount) return null;
    var range = sel.getRangeAt(0);
    if (!article.contains(range.commonAncestorContainer)) return null;
    var nodes = textNodes();
    var off = offsetsOf(range, nodes);
    if (!off) return null;
    var text = flatText(nodes).slice(off.start, off.end);
    if (!text.trim()) return null;
    var anchor = anchorBefore(range);
    return { range: range.cloneRange(), start: off.start, text: text, tex: quoteWithTex(range), anchor: anchor, label: labelOf(anchor) };
  }

  function placeFab() {
    var s = currentSelection();
    if (!s || !panel.hidden) {
      fab.hidden = true;
      return;
    }
    pending = s;
    var rect = s.range.getBoundingClientRect();
    var narrow = window.innerWidth < 640;
    fab.hidden = false;
    if (narrow) {
      fab.style.left = '';
      fab.style.top = '';
      fab.classList.add('ma-fab-bottom');
    } else {
      fab.classList.remove('ma-fab-bottom');
      fab.style.left = Math.max(8, Math.min(window.innerWidth - 120, rect.left + rect.width / 2 - 50)) + 'px';
      fab.style.top = (rect.bottom + window.scrollY + 8) + 'px';
    }
  }

  var timer;
  document.addEventListener('selectionchange', function () {
    clearTimeout(timer);
    timer = setTimeout(placeFab, 180);
  });

  function openPanel(note, editing) {
    panel.innerHTML = '';
    panel.hidden = false;
    fab.hidden = true;
    var q = el('blockquote', 'ma-quote', excerpt(note.text, 400));
    var where = el('p', 'ma-where', note.label ? 'Près de : ' + note.label : '');
    var ta = el('textarea', 'ma-text');
    ta.placeholder = 'Votre commentaire (une erreur, une question, une suggestion…)';
    ta.value = note.comment || '';
    var row = el('div', 'ma-row');
    var keep = el('button', 'ma-btn', editing ? 'Enregistrer' : 'Garder la note');
    var issue = el('button', 'ma-btn ma-btn-primary', 'Ouvrir une issue sur GitHub');
    var cancel = el('button', 'ma-btn ma-btn-quiet', 'Annuler');
    [keep, issue, cancel].forEach(function (b) { b.type = 'button'; row.appendChild(b); });
    var hint = el('p', 'ma-hint', 'La note reste dans ce navigateur. L\'issue s\'ouvre sur GitHub, déjà remplie, et rien n\'est publié tant que vous ne l\'avez pas validée.');
    panel.append(q, where, ta, row, hint);
    ta.focus();

    function store() {
      note.comment = ta.value.trim();
      var notes = load();
      var i = notes.findIndex(function (n) { return n.id === note.id; });
      var clean = { id: note.id, start: note.start, text: note.text, tex: note.tex, anchor: note.anchor, label: note.label, comment: note.comment, date: note.date };
      if (i >= 0) notes[i] = clean; else notes.push(clean);
      save(notes);
      paint();
      renderList();
    }
    keep.onclick = function () { store(); close(); };
    issue.onclick = function () { store(); window.open(issueUrl(note), '_blank', 'noopener'); close(); };
    cancel.onclick = close;
  }

  function close() {
    panel.hidden = true;
    window.getSelection().removeAllRanges();
  }

  fab.addEventListener('mousedown', function (e) { e.preventDefault(); });
  fab.addEventListener('click', function () {
    if (!pending) return;
    var s = pending;
    openPanel({ id: String(Date.now()), start: s.start, text: s.text, tex: s.tex, anchor: s.anchor, label: s.label, comment: '', date: new Date().toISOString() }, false);
  });
  document.addEventListener('keydown', function (e) {
    if (e.key === 'Escape' && !panel.hidden) close();
  });

  // La liste des notes de la page.
  var list = el('div', 'ma-ui ma-list');
  list.hidden = true;
  document.body.appendChild(list);
  listBtn.onclick = function () { list.hidden = !list.hidden; if (!list.hidden) renderList(); };

  function renderList() {
    var notes = load();
    listBtn.textContent = notes.length ? 'Notes (' + notes.length + ')' : 'Notes';
    if (list.hidden) return;
    list.innerHTML = '';
    var head = el('div', 'ma-list-head');
    head.append(el('strong', '', 'Vos notes sur cette page'));
    var x = el('button', 'ma-btn ma-btn-quiet', 'Fermer');
    x.type = 'button';
    x.onclick = function () { list.hidden = true; };
    head.append(x);
    list.append(head);
    if (!notes.length) {
      list.append(el('p', 'ma-hint', 'Sélectionnez un passage du texte, puis « Commenter ».'));
    } else {
      var all = el('button', 'ma-btn ma-btn-primary ma-all', notes.length > 1
        ? 'Une issue pour les ' + notes.length + ' notes'
        : 'Ouvrir une issue');
      all.type = 'button';
      all.onclick = function () { window.open(summaryIssueUrl(load()), '_blank', 'noopener'); };
      list.append(all);
    }
    var nodes = textNodes();
    var text = flatText(nodes);
    notes.forEach(function (n) {
      var item = el('div', 'ma-item');
      item.append(el('blockquote', 'ma-quote', excerpt(n.text, 160)));
      if (n.comment) item.append(el('p', 'ma-comment', n.comment));
      var row = el('div', 'ma-row');
      var go = el('button', 'ma-btn ma-btn-quiet', 'Aller au passage');
      var edit = el('button', 'ma-btn ma-btn-quiet', 'Modifier');
      var iss = el('button', 'ma-btn ma-btn-quiet', 'Issue');
      var del = el('button', 'ma-btn ma-btn-quiet', 'Supprimer');
      [go, edit, iss, del].forEach(function (b) { b.type = 'button'; row.append(b); });
      go.onclick = function () {
        var r = locate(n, nodes, text);
        var target = r ? r.startContainer.parentElement : n.anchor && document.getElementById(n.anchor);
        if (target) target.scrollIntoView({ block: 'center', behavior: 'smooth' });
      };
      edit.onclick = function () { list.hidden = true; openPanel(n, true); };
      iss.onclick = function () { window.open(issueUrl(n), '_blank', 'noopener'); };
      del.onclick = function () { save(load().filter(function (m) { return m.id !== n.id; })); paint(); renderList(); };
      item.append(row);
      list.append(item);
    });
  }

  // KaTeX compose les formules à DOMContentLoaded, dans un gestionnaire
  // enregistré avant celui-ci : on surligne juste après, sans attendre les
  // polices ni les images.
  function start() { paint(); renderList(); }
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', function () { setTimeout(start, 0); });
  } else {
    setTimeout(start, 0);
  }
})();
