#!/usr/bin/env node
/**
 * Transforme les `.tex` de `lecons/` en vues de lecture HTML, et construit
 * l'index du site dans `dist/`.
 *
 *   npm run render
 *
 * Même moteur que grothendieck-project (scripts/render.mjs) : le `.tex` est la
 * source de référence, la vue HTML en est dérivée et jamais l'inverse. Les
 * mathématiques ne sont pas converties : les délimiteurs passent tels quels et
 * KaTeX les compose dans le navigateur, avec les macros du préambule. L'écran
 * et le PDF viennent donc de la même source.
 *
 * Le rendu couvre un **sous-ensemble restreint** de LaTeX : celui des articles
 * (amsthm, listes, tableaux booktabs, renvois, bibliographie). Tout ce qui en
 * sort fait échouer le rendu, avec le fichier et le passage en cause : un
 * convertisseur qui accepterait tout aplatirait en silence ce qu'il ne
 * comprend pas.
 *
 * Différence avec le moteur des transcriptions : les environnements peuvent
 * s'imbriquer (une liste dans un exemple, une formule dans une liste), d'où un
 * analyseur récursif ; et il y a des compteurs, des numéros et des renvois.
 */

import { copyFile, cp, mkdir, readdir, readFile, rm, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { basename, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import katex from 'katex';

const ROOT = resolve(import.meta.dirname, '..');
const SOURCE = resolve(ROOT, 'lecons');
const OUT = resolve(ROOT, 'dist');

// ---------------------------------------------------------------------------
// Utilitaires.

export const escapeHtml = (s) =>
  s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
const escapeAttr = (s) => escapeHtml(s).replace(/"/g, '&quot;');

/** Indice de l'accolade fermante qui correspond à celle en `open`. */
function matchBrace(s, open, l = '{', r = '}') {
  let depth = 0;
  for (let i = open; i < s.length; i++) {
    if (s[i] === '\\') {
      i++;
      continue;
    }
    if (s[i] === l) depth++;
    else if (s[i] === r && --depth === 0) return i;
  }
  throw new Error(`accolade non fermée après « ${s.slice(open, open + 60)} »`);
}

/** Lit un argument `{…}` à partir de `i` (espaces sautés). */
function readGroup(s, i) {
  while (/\s/.test(s[i] ?? '')) i++;
  if (s[i] !== '{') return null;
  const j = matchBrace(s, i);
  return { arg: s.slice(i + 1, j), end: j + 1 };
}

/** Lit un argument optionnel `[…]` à partir de `i`. */
function readOptional(s, i) {
  let k = i;
  while (s[k] === ' ' || s[k] === '\t') k++;
  if (s[k] !== '[') return null;
  const j = matchBrace(s, k, '[', ']');
  return { arg: s.slice(k + 1, j), end: j + 1 };
}

/** Quelques mots autour d'une position, pour qu'une erreur se retrouve dans le fichier. */
const around = (s, i) => s.slice(Math.max(0, i - 50), i + 50).replace(/\s+/g, ' ').trim();

// ---------------------------------------------------------------------------
// Le préambule : macros, théorèmes, titre.

function readPreamble(pre) {
  const macros = {};
  const theorems = {};
  let style = 'plain';

  const cmd = /\\(newcommand|renewcommand|providecommand|DeclareMathOperator\*?|theoremstyle|newtheorem)(?![a-zA-Z])/g;
  let m;
  while ((m = cmd.exec(pre))) {
    let i = m.index + m[0].length;
    if (m[1] === 'theoremstyle') {
      const g = readGroup(pre, i);
      style = g.arg.trim();
      cmd.lastIndex = g.end;
    } else if (m[1] === 'newtheorem') {
      // \newtheorem{env}[partagé]{Nom}[dans]  ou  \newtheorem{env}{Nom}[dans]
      const env = readGroup(pre, i);
      i = env.end;
      const shared = readOptional(pre, i);
      if (shared) i = shared.end;
      const name = readGroup(pre, i);
      i = name.end;
      const within = !shared && readOptional(pre, i);
      if (within) i = within.end;
      theorems[env.arg] = {
        name: name.arg,
        style,
        counter: shared ? shared.arg : env.arg,
        within: within ? within.arg : null,
      };
      cmd.lastIndex = i;
    } else if (m[1].startsWith('DeclareMathOperator')) {
      const name = readGroup(pre, i);
      const body = readGroup(pre, name.end);
      macros[name.arg.trim()] = m[1].endsWith('*')
        ? `\\operatorname*{${body.arg}}`
        : `\\operatorname{${body.arg}}`;
      cmd.lastIndex = body.end;
    } else {
      // \newcommand{\nom}[n]{corps} ; KaTeX déduit n des #k du corps.
      const name = readGroup(pre, i);
      i = name.end;
      const n = readOptional(pre, i);
      if (n) i = n.end;
      if (readOptional(pre, i)) {
        throw new Error(`${name.arg} : argument optionnel par défaut non pris en charge`);
      }
      const body = readGroup(pre, i);
      macros[name.arg.trim()] = body.arg;
      cmd.lastIndex = body.end;
    }
  }

  const field = (name) => {
    const at = pre.search(new RegExp(`\\\\${name}\\s*\\{`));
    return at === -1 ? '' : readGroup(pre, at + name.length + 1).arg;
  };
  return { macros, theorems, title: field('title'), author: field('author'), date: field('date') };
}

// ---------------------------------------------------------------------------
// Les mathématiques, mises de côté avant tout le reste.

const marker = (i) => `MATH${i}`;
const MARKED = () => /MATH(\d+)/g;

/**
 * Les formules sortent du texte avant l'échappement, l'expansion des macros et
 * le découpage en paragraphes, qui les corrompraient tous trois. Les formules
 * numérotées reçoivent ici leur numéro, et leurs `\label` sont enregistrés :
 * KaTeX ne connaît pas `\label`.
 */
function liftMath(tex, doc, held = []) {
  const keep = (raw, display, id) => {
    held.push({ raw, display, id });
    return marker(held.length - 1);
  };

  const display = (body, numbered) => {
    let raw = body;
    const labels = [...raw.matchAll(/\\label\{([^{}]*)\}/g)].map((x) => x[1]);
    // \qedhere place le ∎ dans la formule ; ici il reste en fin de preuve.
    raw = raw.replace(/\\label\{[^{}]*\}/g, '').replace(/\\qedhere\b/g, '');
    if (/\\(?:nonumber|notag)\b/.test(raw)) throw new Error('\\nonumber/\\notag non pris en charge');
    let id = null;
    if (numbered) {
      const tag = /\\tag\{([^{}]*)\}/.exec(raw);
      const num = tag ? tag[1] : String(++doc.equation);
      if (!tag) raw += `\\tag{${num}}`;
      id = `eq-${doc.ids++}`;
      for (const l of labels) doc.define(l, num, id, 'eq');
    } else if (labels.length) {
      throw new Error(`\\label{${labels[0]}} dans une formule non numérotée`);
    }
    return keep(raw, true, id);
  };

  const out = tex
    .replace(/\\begin\{(equation|align|gather|multline)(\*?)\}([\s\S]*?)\\end\{\1\2\}/g,
      (all, env, star, body) => {
        if (env !== 'equation' && !star) {
          throw new Error(`\\begin{${env}} numéroté non pris en charge (utiliser ${env}*)`);
        }
        const inner = env === 'align' ? `\\begin{aligned}${body}\\end{aligned}`
          : env === 'gather' ? `\\begin{gathered}${body}\\end{gathered}`
            : env === 'multline' ? `\\begin{gathered}${body}\\end{gathered}`
              : body;
        return display(inner, env === 'equation' && !star);
      })
    .replace(/\\\[([\s\S]*?)\\\]/g, (_, m) => display(m, false))
    .replace(/\$\$([\s\S]*?)\$\$/g, (_, m) => display(m, false))
    .replace(/\\\(([\s\S]*?)\\\)/g, (_, m) => keep(m, false))
    .replace(/(?<!\\)\$((?:[^$\\]|\\.)+)\$/g, (_, m) => {
      if (/\\label\{/.test(m)) throw new Error('\\label dans une formule en ligne');
      return keep(m, false);
    });
  return { text: out, held };
}

/**
 * Chaque formule est composée une fois ici, avec `throwOnError`, sans que le
 * résultat serve : le navigateur la recompose. Avec `throwOnError: false` côté
 * client, une formule que KaTeX refuse s'affiche en rouge sans faire échouer
 * quoi que ce soit ; ce passage fait échouer le rendu à la place.
 */
function checkMath(held, macros) {
  for (const { raw, display } of held) {
    try {
      katex.renderToString(raw, { displayMode: display, throwOnError: true, macros: { ...macros }, strict: 'ignore' });
    } catch (e) {
      throw new Error(`KaTeX refuse « ${raw.trim().slice(0, 80)} » : ${e.message.split('\n')[0]}`);
    }
  }
}

function dropMathBack(html, held) {
  return html.replace(MARKED(), (_, i) => {
    const { raw, display, id } = held[Number(i)];
    const body = escapeHtml(raw);
    return display
      ? `<span class="ltx_Math ltx_display"${id ? ` id="${id}"` : ''}>\\[${body}\\]</span>`
      : `<span class="ltx_Math">\\(${body}\\)</span>`;
  });
}

// ---------------------------------------------------------------------------
// Le texte courant.

/** Macros à un argument, remplacées par appariement d'accolades. */
const BRACED = {
  emph: (a) => `<em class="ltx_emph">${a}</em>`,
  textit: (a) => `<em class="ltx_emph">${a}</em>`,
  textsl: (a) => `<em class="ltx_emph">${a}</em>`,
  textbf: (a) => `<strong class="ltx_text ltx_font_bold">${a}</strong>`,
  textsf: (a) => `<span class="ltx_text ltx_font_sansserif">${a}</span>`,
  textsc: (a) => `<span class="ltx_text ltx_font_smallcaps">${a}</span>`,
  texttt: (a) => `<code class="ltx_text ltx_font_typewriter">${a}</code>`,
  textup: (a) => a,
  textrm: (a) => a,
  textnormal: (a) => a,
  mbox: (a) => a,
  underline: (a) => `<u>${a}</u>`,
  textsuperscript: (a) => `<sup>${a}</sup>`,
  url: (a) => `<a class="ltx_url" href="${a}">${a}</a>`,
};
/** Macros à deux arguments. */
const BRACED2 = {
  href: (url, text) => `<a class="ltx_href" href="${url}">${text}</a>`,
  texorpdfstring: (tex) => tex,
};

/** Macros sans argument, sur du texte déjà échappé. */
const TOKENS = [
  [/\\ldots(\{\})?|\\dots(\{\})?|\\textellipsis(\{\})?/g, '…'],
  [/\\og\{?\}?\s*/g, '« '],
  [/\s*\\fg\{?\}?/g, ' »'],
  [/\\S(?![a-zA-Z])\s*/g, '§&#8239;'],
  [/\\(?:noindent|par|medskip|bigskip|smallskip|newpage|clearpage|hfill|centering|large|Large|LARGE|small|footnotesize|normalsize|nobreak|allowbreak)(?![a-zA-Z])\s*/g, ''],
  [/\\\\(\[[^\]]*\])?/g, '<br>'],
  [/\\[ ,;:!]/g, ' '],
  [/\\\//g, ''],
  [/\\q?quad(?![a-zA-Z])/g, '  '],
  [/\\%/g, '%'],
  [/\\&amp;/g, '&amp;'],
  [/\\_/g, '_'],
  [/\\#/g, '#'],
  [/\\\{/g, '&#123;'],
  [/\\\}/g, '&#125;'],
  [/---/g, '—'],
  [/--/g, '–'],
  [/``/g, '“'],
  [/''/g, '”'],
  [/~/g, '&nbsp;'],
];

function expandBraced(text) {
  let out = text;
  let changed = true;
  while (changed) {
    changed = false;
    const re = /\\([a-zA-Z]+)\s*\{/g;
    let m;
    while ((m = re.exec(out))) {
      const name = m[1];
      const open = m.index + m[0].length - 1;
      if (name in BRACED) {
        const j = matchBrace(out, open);
        out = out.slice(0, m.index) + BRACED[name](out.slice(open + 1, j)) + out.slice(j + 1);
        changed = true;
        break;
      }
      if (name in BRACED2) {
        const j = matchBrace(out, open);
        const second = readGroup(out, j + 1);
        if (!second) throw new Error(`\\${name} attend deux arguments`);
        out = out.slice(0, m.index)
          + BRACED2[name](out.slice(open + 1, j), second.arg) + out.slice(second.end);
        changed = true;
        break;
      }
    }
  }
  return out;
}

/** Renvois : un repère, résolu quand tous les numéros sont connus. */
const refMark = (kind, key) => `${kind}:${key}`;

function inline(text, doc) {
  let out = escapeHtml(text);

  out = out
    .replace(/\\label\{([^{}]*)\}/g, (_, k) => {
      doc.labelHere(k);
      return '';
    })
    .replace(/\\(eqref|ref|pageref|autoref)\{([^{}]*)\}/g, (_, kind, k) => refMark(kind, k))
    .replace(/\\cite(?:\[([^\]]*)\])?\{([^{}]*)\}/g, (_, note, keys) =>
      `[${keys.split(',').map((k) => refMark('cite', k.trim())).join(', ')}${note ? `, ${note}` : ''}]`);

  out = expandBraced(out);
  for (const [re, to] of TOKENS) out = out.replace(re, to);
  // Accolades de groupement restantes : sans effet à l'écran.
  out = out.replace(/(?<!\\)[{}]/g, '');

  const stray = /\\([a-zA-Z@]+|.)/.exec(out);
  if (stray) {
    throw new Error(`commande non prise en charge \\${stray[1]} dans « ${around(out, stray.index)} »`);
  }
  return out;
}

// ---------------------------------------------------------------------------
// Les blocs.

/** Trouve le `\end{name}` qui ferme le `\begin{name}` dont le contenu commence en `from`. */
function matchEnd(text, name, from) {
  const re = new RegExp(`\\\\(begin|end)\\{${name.replace('*', '\\*')}\\}`, 'g');
  re.lastIndex = from;
  let depth = 1;
  let m;
  while ((m = re.exec(text))) {
    depth += m[1] === 'begin' ? 1 : -1;
    if (depth === 0) return { start: m.index, end: m.index + m[0].length };
  }
  throw new Error(`\\begin{${name}} sans \\end{${name}}, après « ${around(text, from)} »`);
}

/** Découpe une liste en items, au premier niveau seulement. */
function splitItems(body) {
  const items = [];
  let depth = 0;
  let cur = null;
  const re = /\\(begin|end)\{[^{}]*\}|\\item(?![a-zA-Z])/g;
  let last = 0;
  let m;
  while ((m = re.exec(body))) {
    if (m[1] === 'begin') depth++;
    else if (m[1] === 'end') depth--;
    else if (depth === 0) {
      if (cur !== null) items.push(body.slice(cur, m.index));
      else if (body.slice(last, m.index).trim()) {
        throw new Error(`texte avant le premier \\item : « ${around(body, 0)} »`);
      }
      cur = m.index + m[0].length;
    }
  }
  if (cur !== null) items.push(body.slice(cur));
  return items;
}

/** Un seul paragraphe dans un item : on le déballe, pour garder la liste compacte. */
function unwrapSingle(blocks) {
  const html = blocks.join('\n');
  const one = /^<p class="ltx_p">([\s\S]*)<\/p>$/.exec(html);
  return one && !one[1].includes('<p ') ? one[1] : html;
}

const SECTIONING = /\\(section|subsection|subsubsection|paragraph)(\*?)\s*\{/g;

function paragraphs(text, doc) {
  // Chaque titre commence un bloc ; celui d'une section ou sous-section le
  // termine aussi, un \paragraph court jusqu'à la fin du paragraphe.
  let cut = '';
  let from = 0;
  let m;
  const re = new RegExp(SECTIONING.source, 'g');
  while ((m = re.exec(text))) {
    const close = matchBrace(text, m.index + m[0].length - 1);
    cut += `${text.slice(from, m.index)}\n\n${text.slice(m.index, close + 1)}`;
    if (m[1] !== 'paragraph') cut += '\n\n';
    from = close + 1;
    re.lastIndex = close + 1;
  }
  cut += text.slice(from);

  const out = [];
  for (const raw of cut.split(/\n\s*\n+/)) {
    let block = raw.trim();
    if (!block) continue;

    if (/^\\maketitle$/.test(block)) {
      out.push(doc.titleBlock());
      continue;
    }
    if (/^\\tableofcontents$/.test(block)) {
      out.push('TOC');
      continue;
    }

    const head = /^\\(section|subsection|subsubsection)(\*?)\s*\{/.exec(block);
    if (head) {
      const close = matchBrace(block, head[0].length - 1);
      const rest = block.slice(close + 1).trim();
      out.push(doc.heading(head[1], !!head[2], block.slice(head[0].length, close)));
      if (rest) out.push(...paragraphs(rest, doc));
      continue;
    }

    let runin = '';
    const par = /^\\paragraph(\*?)\s*\{/.exec(block);
    if (par) {
      const close = matchBrace(block, par[0].length - 1);
      runin = `<span class="ltx_runin ltx_font_bold">${inline(block.slice(par[0].length, close), doc)}</span>`;
      block = block.slice(close + 1).trim();
    }
    const body = inline(block, doc);
    if (body.trim() || runin) out.push(`<p class="ltx_p">${runin}${body}</p>`);
  }
  return out;
}

/** Un texte qui peut contenir des environnements, à tout niveau. */
function blocks(text, doc) {
  const out = [];
  const re = /\\begin\{([a-zA-Z*]+)\}/g;
  let pos = 0;
  let m;
  while ((m = re.exec(text))) {
    out.push(...paragraphs(text.slice(pos, m.index), doc));
    const close = matchEnd(text, m[1], m.index + m[0].length);
    out.push(...environment(m[1], text.slice(m.index + m[0].length, close.start), doc));
    pos = close.end;
    re.lastIndex = close.end;
  }
  out.push(...paragraphs(text.slice(pos), doc));
  return out;
}

function environment(name, inner, doc) {
  const thm = doc.theorems[name];
  if (thm) return doc.theorem(name, thm, inner);

  switch (name) {
    case 'abstract':
      return [`<div class="ltx_abstract"><h6 class="ltx_title ltx_title_abstract">Résumé</h6>${blocks(inner, doc).join('\n')}</div>`];

    case 'proof': {
      const opt = readOptional(inner, 0);
      const title = opt ? inline(opt.arg, doc) : 'Démonstration';
      const body = blocks(opt ? inner.slice(opt.end) : inner, doc);
      const qed = '<span class="ltx_qed">∎</span>';
      const last = body.length - 1;
      if (last >= 0 && body[last].endsWith('</p>')) body[last] = body[last].slice(0, -4) + ` ${qed}</p>`;
      else body.push(`<p class="ltx_p">${qed}</p>`);
      const h = `<span class="ltx_title ltx_runin ltx_font_italic ltx_title_proof">${title}.</span>`;
      return [`<div class="ltx_proof">${runIn(h, body)}</div>`];
    }

    case 'itemize':
    case 'enumerate': {
      const opt = readOptional(inner, 0);
      const items = splitItems(opt ? inner.slice(opt.end) : inner);
      const tag = name === 'itemize' ? 'ul' : 'ol';
      let tagged = false;
      const lis = items.map((raw, k) => {
        const lab = readOptional(raw, 0);
        const body = lab ? raw.slice(lab.end) : raw;
        if (name === 'enumerate') doc.target(String(k + 1), null);
        const html = unwrapSingle(blocks(body.trim(), doc));
        if (!lab) return `<li class="ltx_item">${html}</li>`;
        tagged = true;
        return `<li class="ltx_item ltx_item_tagged"><span class="ltx_tag">${inline(lab.arg, doc)}</span> ${html}</li>`;
      });
      return [`<${tag} class="ltx_itemize${tagged ? ' ltx_itemize_tagged' : ''}">${lis.join('\n')}</${tag}>`];
    }

    case 'center':
      return [`<div class="ltx_align_center">${blocks(inner.replace(/\\renewcommand\{\\arraystretch\}\{[^{}]*\}/g, ''), doc).join('\n')}</div>`];

    case 'quote':
    case 'quotation':
      return [`<blockquote class="ltx_quote">${blocks(inner, doc).join('\n')}</blockquote>`];

    case 'tabular':
      return [tabular(inner, doc)];

    case 'thebibliography':
      return [doc.bibliography(inner)];

    default:
      throw new Error(`environnement non pris en charge \\begin{${name}} — étendre scripts/render.mjs`);
  }
}

/** Le titre d'un énoncé, en tête de son premier paragraphe. */
function runIn(heading, body) {
  if (body.length && body[0].startsWith('<p class="ltx_p">')) {
    return [body[0].replace('<p class="ltx_p">', `<p class="ltx_p">${heading} `), ...body.slice(1)].join('\n');
  }
  return [`<p class="ltx_p">${heading}</p>`, ...body].join('\n');
}

function tabular(inner, doc) {
  const spec = readGroup(inner, 0);
  if (!spec) throw new Error('\\begin{tabular} sans spécification de colonnes');
  const rows = [];
  let head = true;
  let sawMid = false;
  for (let row of spec ? inner.slice(spec.end).split(/\\\\(?:\[[^\]]*\])?/) : []) {
    if (/\\midrule/.test(row)) sawMid = true;
    row = row.replace(/\\(toprule|midrule|bottomrule|hline)/g, '').trim();
    if (!row) {
      if (sawMid) head = false;
      continue;
    }
    if (sawMid) head = false;
    const cells = row.replace(/\\&/g, '').split('&').map((c) => c.replace(//g, '\\&'));
    rows.push({ head, cells });
  }
  // Sans \midrule, il n'y a pas de ligne d'en-tête.
  if (!sawMid) for (const r of rows) r.head = false;
  const tr = (r) => `<tr>${r.cells.map((c) => {
    const t = r.head ? 'th' : 'td';
    return `<${t} class="ltx_${t}">${inline(c.trim(), doc)}</${t}>`;
  }).join('')}</tr>`;
  const thead = rows.filter((r) => r.head).map(tr).join('');
  const tbody = rows.filter((r) => !r.head).map(tr).join('');
  return `<table class="ltx_tabular">${thead ? `<thead>${thead}</thead>` : ''}<tbody>${tbody}</tbody></table>`;
}

// ---------------------------------------------------------------------------
// Le document : compteurs, renvois, titre, table des matières.

function makeDoc(pre) {
  const doc = {
    ...pre,
    ids: 0,
    equation: 0,
    section: 0,
    subsection: 0,
    counters: {},
    labels: {},
    toc: [],
    bib: {},
    current: null,
    define(key, num, id, kind) {
      if (key in this.labels) throw new Error(`\\label{${key}} défini deux fois`);
      this.labels[key] = { num, id, kind };
    },
    target(num, id) {
      this.current = { num, id };
    },
    labelHere(key) {
      if (!this.current) throw new Error(`\\label{${key}} sans rien à numéroter avant lui`);
      const id = this.current.id ?? `lbl-${this.ids++}`;
      this.define(key, this.current.num, id, 'ref');
    },
    heading(level, star, title) {
      const html = inline(title, this);
      if (level === 'subsubsection') throw new Error('\\subsubsection non prise en charge');
      let num = null;
      if (!star) {
        if (level === 'section') {
          this.section++;
          this.subsection = 0;
          for (const [env, t] of Object.entries(this.theorems)) {
            if (t.within === 'section') this.counters[env] = 0;
          }
          num = String(this.section);
        } else {
          this.subsection++;
          num = `${this.section}.${this.subsection}`;
        }
      }
      const id = num ? `s${num}` : `s-${this.ids++}`;
      this.target(num, id);
      this.toc.push({ level, num, html, id });
      const tag = level === 'section' ? 'h2' : 'h3';
      const cls = level === 'section' ? 'ltx_title_section' : 'ltx_title_subsection';
      return `<${tag} class="ltx_title ${cls}" id="${id}">${num ? `<span class="ltx_tag ltx_tag_${level}">${num} </span>` : ''}${html}</${tag}>`;
    },
    theorem(env, thm, inner) {
      const counter = thm.counter;
      const def = this.theorems[counter];
      if (!def) throw new Error(`compteur de théorème inconnu « ${counter} »`);
      this.counters[counter] = (this.counters[counter] ?? 0) + 1;
      const n = this.counters[counter];
      const num = def.within === 'section' ? `${this.section}.${n}` : String(n);
      const id = `${env}-${num}`;
      const opt = readOptional(inner, 0);
      this.target(num, id);
      const note = opt ? ` (${inline(opt.arg, this)})` : '';
      const body = blocks(opt ? inner.slice(opt.end) : inner, this);
      const h = `<span class="ltx_title ltx_runin ltx_title_theorem"><span class="ltx_tag">${escapeHtml(thm.name)} ${num}</span>${note}.</span>`;
      const italic = thm.style === 'plain' ? ' ltx_theorem_plain' : '';
      return [`<div class="ltx_theorem ltx_theorem_${env}${italic}" id="${id}">${runIn(h, body)}</div>`];
    },
    bibliography(inner) {
      const width = readGroup(inner, 0);
      const parts = (width ? inner.slice(width.end) : inner).split(/\\bibitem(?![a-zA-Z])/).slice(1);
      const items = parts.map((p, k) => {
        const key = readGroup(p, 0);
        if (!key) throw new Error('\\bibitem sans clé');
        const n = String(k + 1);
        this.bib[key.arg.trim()] = n;
        return `<li class="ltx_bibitem" id="bib-${escapeAttr(key.arg.trim())}"><span class="ltx_tag ltx_tag_bibitem">[${n}]</span> ${inline(p.slice(key.end).trim(), this)}</li>`;
      });
      this.toc.push({ level: 'section', num: null, html: 'Références', id: 'bib' });
      return `<section class="ltx_bibliography" id="bib"><h2 class="ltx_title ltx_title_bibliography">Références</h2><ul class="ltx_biblist">${items.join('\n')}</ul></section>`;
    },
    titleBlock() {
      const [main, ...sub] = this.title.split(/\\\\(?:\[[^\]]*\])?/);
      return `<h1 class="ltx_title ltx_title_document">${inline(main.trim(), this)}`
        + (sub.length ? `<br><span class="ltx_subtitle">${inline(sub.join(' ').trim(), this)}</span>` : '')
        + '</h1>'
        + (this.author ? `<div class="ltx_authors"><span class="ltx_creator ltx_role_author">${inline(this.author, this)}</span></div>` : '')
        + (this.date ? `<div class="ltx_dates">${inline(this.date, this)}</div>` : '');
    },
  };
  return doc;
}

function resolveRefs(html, doc, file) {
  const missing = [];
  const out = html.replace(/([a-z]+):([^]*)/g, (_, kind, key) => {
    if (kind === 'cite') {
      const n = doc.bib[key];
      if (!n) return missing.push(`\\cite{${key}}`), '??';
      return `<a class="ltx_ref" href="#bib-${escapeAttr(key)}">${n}</a>`;
    }
    const l = doc.labels[key];
    if (!l) return missing.push(`\\${kind}{${key}}`), '??';
    const a = `<a class="ltx_ref" href="#${l.id}">${escapeHtml(l.num ?? '?')}</a>`;
    return kind === 'eqref' ? `(${a})` : a;
  });
  if (missing.length) throw new Error(`${file} : renvois sans étiquette ${missing.join(', ')}`);
  return out;
}

function tocHtml(doc) {
  const entries = doc.toc.map((e) =>
    `<li class="ltx_tocentry ltx_tocentry_${e.level}"><a class="ltx_ref" href="#${e.id}">`
    + `${e.num ? `<span class="ltx_tag">${e.num}</span> ` : ''}${e.html}</a></li>`);
  return `<nav class="ltx_TOC"><h6 class="ltx_title ltx_title_contents">Table des matières</h6><ul class="ltx_toclist">${entries.join('\n')}</ul></nav>`;
}

export function render(tex, file) {
  const at = tex.indexOf('\\begin{document}');
  const end = tex.lastIndexOf('\\end{document}');
  if (at === -1 || end === -1) throw new Error('pas de \\begin{document} … \\end{document}');

  const pre = readPreamble(tex.slice(0, at).replace(/(?<!\\)%.*$/gm, ''));
  const doc = makeDoc(pre);
  const body = tex.slice(at + '\\begin{document}'.length, end).replace(/(?<!\\)%.*$/gm, '');
  if (/\\footnote\b/.test(body)) throw new Error('\\footnote non pris en charge pour l\'instant');

  // Le titre et l'auteur peuvent contenir des formules : levées avec le corps.
  const held = [];
  for (const k of ['title', 'author', 'date']) doc[k] = liftMath(doc[k], doc, held).text;
  const { text } = liftMath(body, doc, held);
  let html = blocks(text, doc).join('\n');
  html = html.replace('TOC', () => tocHtml(doc));
  html = resolveRefs(html, doc, file);
  checkMath(held, pre.macros);
  html = dropMathBack(html, held);

  const plainTitle = pre.title.split(/\\\\/)[0].replace(/\$([^$]*)\$/g, '$1')
    .replace(/\\([a-zA-Z]+)/g, (_, c) => (c === 'sqrt' ? '√' : pre.macros[`\\${c}`] ?? '').replace(/\\mathbb\{(.)\}/, '$1'))
    .replace(/[{}]/g, '').replace(/\s+/g, ' ').trim();
  return { html, title: plainTitle, macros: pre.macros };
}

// ---------------------------------------------------------------------------
// Les pages.

const STYLE = `
  :root {
    color-scheme: light;
    --serif: 'Iowan Old Style', 'Palatino Linotype', Palatino, Georgia, 'Times New Roman', serif;
    --sans: -apple-system, BlinkMacSystemFont, 'Segoe UI', Inter, Roboto, Helvetica, Arial, sans-serif;
    --mono: 'SF Mono', ui-monospace, Menlo, Consolas, 'Liberation Mono', monospace;
    --text-font-family: var(--serif);
    --headings-font-family: var(--sans);
    --ink: #12120f; --ink2: #3f3e3a; --ink3: #6f6d66; --ink4: #9a988f;
    --rule: #e2e0da; --rule2: #eeece7; --surf3: #f4f2ed; --accent: #38539d;
  }
  body { box-sizing: border-box; margin: 0; background: #fff; color: var(--ink);
         font-family: var(--serif); font-size: 17px; line-height: 1.6; }
  /* ar5iv donne à .ltx_page_main une largeur fixe ; en content-box, le padding débordait. */
  .ltx_page_main { box-sizing: border-box; width: auto; max-width: 46rem; margin: 0 auto; padding: 1rem 1rem 4rem; }
  .ltx_document { width: auto; max-width: 100%; }
  .ltx_p { font-size: 17px; line-height: 1.62; }
  .ltx_title { font-family: var(--sans); }
  .ltx_title_document { font-size: 1.9rem; line-height: 1.2; margin-top: 1.2rem; }
  .ltx_subtitle { font-size: 1.05rem; font-weight: 500; color: var(--ink2); }
  .ltx_authors, .ltx_dates { font-family: var(--sans); font-size: 14px; color: var(--ink3); }
  .ltx_theorem_plain > .ltx_p, .ltx_theorem_plain li { font-style: italic; }
  .ltx_theorem_plain .ltx_title_theorem, .ltx_theorem_plain .ltx_ref { font-style: normal; }
  .ltx_title_proof { font-weight: 600; }
  .ltx_qed { float: right; color: var(--ink3); }
  .ltx_Math.ltx_display { display: block; margin: .9rem 0; text-align: center;
                          max-width: 100%; overflow-x: auto; overflow-y: hidden; }
  .ltx_align_center { text-align: center; }
  .ltx_tabular { margin: 1.2rem auto; border-collapse: collapse; font-size: 15px; text-align: left; }
  .ltx_tabular th { font-family: var(--sans); font-size: 12px; font-weight: 700; letter-spacing: .05em;
                    text-transform: uppercase; color: var(--ink3); padding: 0 12px 8px 0;
                    border-bottom: 1px solid var(--ink3); }
  .ltx_tabular td { padding: 6px 12px 6px 0; border-top: 1px solid var(--rule2); vertical-align: top; }
  .ltx_tabular tbody tr:last-child td { border-bottom: 1px solid var(--ink3); }
  .ltx_biblist { list-style: none; padding: 0; }
  .ltx_bibitem { margin-bottom: .5rem; font-size: 15px; }
  .ltx_tag_bibitem { color: var(--ink3); font-family: var(--sans); font-size: 13px; }
  a.ltx_ref { color: var(--accent); text-decoration: none; }
  .ltx_itemize_tagged { list-style: none; }
  .ma-nav { position: sticky; top: 0; z-index: 2; background: rgba(255,255,255,.94);
            backdrop-filter: blur(6px); border-bottom: 1px solid var(--rule);
            font-family: var(--sans); font-size: 13px; }
  .ma-nav-in { max-width: 46rem; margin: 0 auto; padding: .55rem 1rem;
               display: flex; flex-wrap: wrap; gap: .4rem 1rem; align-items: center; }
  .ma-nav a { color: var(--ink2); text-decoration: none; }
  .ma-nav a:hover { color: var(--accent); }
  .ma-nav .ma-crumb { color: var(--ink3); margin-right: auto; }
  .ma-nav .ma-crumb a { color: var(--ink3); }
  @media (max-width: 40rem) { body, .ltx_p { font-size: 16px; } .ltx_title_document { font-size: 1.5rem; } }
`;

function nav(rootRel, crumb, links) {
  return `<header class="ma-nav"><div class="ma-nav-in">
<span class="ma-crumb"><a href="${rootRel}index.html">Leçons</a> / ${crumb}</span>
${links.map(([href, text]) => `<a href="${href}">${text}</a>`).join('\n')}
</div></header>`;
}

function readingPage({ title, html, macros, rootRel, crumb, links }) {
  return `<!doctype html>
<html lang="fr" data-theme="light">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>${escapeHtml(title)}</title>
<link rel="stylesheet" href="${rootRel}vendor/ar5iv.css">
<link rel="stylesheet" href="${rootRel}vendor/katex/katex.min.css">
<style>${STYLE}</style>
</head>
<body>
${nav(rootRel, crumb, links)}
<main class="ltx_page_main">
<article class="ltx_document">
${html}
</article>
</main>
<script defer src="${rootRel}vendor/katex/katex.min.js"></script>
<script defer src="${rootRel}vendor/katex/auto-render.min.js"></script>
<script>
// Les macros du préambule, pour que KaTeX compose les mêmes formules que le PDF.
var MACROS = ${JSON.stringify(macros).replace(/</g, '\\u003c')};
document.addEventListener('DOMContentLoaded', function () {
  renderMathInElement(document.body, {
    delimiters: [
      { left: '\\\\[', right: '\\\\]', display: true },
      { left: '\\\\(', right: '\\\\)', display: false },
    ],
    throwOnError: false,
    macros: MACROS,
  });
  if (location.hash) {
    var t = document.getElementById(decodeURIComponent(location.hash.slice(1)));
    if (t) requestAnimationFrame(function () { t.scrollIntoView({ block: 'start' }); });
  }
});
</script>
</body>
</html>
`;
}

function sourcePage({ text, file, rootRel, crumb, links, kind }) {
  return `<!doctype html>
<html lang="fr">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>${escapeHtml(file)} — source ${kind}</title>
<style>${STYLE}
  pre { white-space: pre-wrap; word-break: break-word; margin: 0;
        font: 13px/1.6 var(--mono); color: var(--ink2); }
  .ma-src-head { font-family: var(--sans); font-size: 13px; color: var(--ink3); margin: 1rem 0 1.2rem; }
</style>
</head>
<body>
${nav(rootRel, crumb, links)}
<main class="ltx_page_main">
<p class="ma-src-head">Source ${kind} de référence, ${escapeHtml(file)} — <a href="./${escapeAttr(file)}" download>télécharger le fichier</a></p>
<pre>${escapeHtml(text)}</pre>
</main>
</body>
</html>
`;
}

// ---------------------------------------------------------------------------
// L'index.

/** Les numéros de leçon cités dans « Leçons concernées ». */
function citedLecons(tex) {
  const m = /\\paragraph\{Leçons concernées\.?\}([^\n]*(?:\n(?!\s*\n)[^\n]*)*)/.exec(tex);
  return m ? [...new Set([...m[1].matchAll(/\b([12]\d\d)\b/g)].map((x) => x[1]))] : [];
}

function indexPage({ lecons, folders, missing }) {
  const byNum = Object.fromEntries(lecons.map((l) => [l.numero, l]));
  const uses = {};
  for (const f of folders) {
    for (const d of f.docs) {
      for (const n of d.cited) if (n !== f.numero) (uses[n] ??= []).push({ f, d });
    }
  }

  const card = (f) => `
<section class="ix-lecon" id="lecon-${f.numero}">
  <h2><span class="ix-num">${f.numero}</span> ${escapeHtml(byNum[f.numero].intitule)}</h2>
  <ul class="ix-docs">
  ${f.docs.map((d) => `<li>
    <a class="ix-doc-title" href="${d.href}">${escapeHtml(d.title)}</a>
    <span class="ix-links">
      <a href="${d.href}">Lire</a>
      ${d.pdf ? `<a href="${d.pdf}">PDF</a>` : ''}
      <a href="${d.src}">Source LaTeX</a>
      ${d.lean.map((l) => `<a href="${l.href}">Lean · ${escapeHtml(l.name)}</a>`).join('\n      ')}
    </span>
    ${d.cited.filter((n) => n !== f.numero).length ? `<span class="ix-also">Sert aussi pour ${d.cited.filter((n) => n !== f.numero).map((n) => `<a href="#autres-${n}">${n}</a>`).join(', ')}</span>` : ''}
  </li>`).join('\n')}
  </ul>
</section>`;

  const others = Object.keys(uses).sort().map((n) => `
  <li id="autres-${n}"><span class="ix-num">${n}</span> ${escapeHtml(byNum[n]?.intitule ?? '')}
    <span class="ix-also">${uses[n].map(({ f, d }) => `<a href="${d.href}">${escapeHtml(d.title)}</a> (${f.numero})`).join(' · ')}</span></li>`).join('');

  const alg = folders.filter((f) => f.numero < '200');
  const ana = folders.filter((f) => f.numero >= '200');

  return `<!doctype html>
<html lang="fr">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Leçons d'agrégation</title>
<style>${STYLE}
  .ix-main { max-width: 52rem; margin: 0 auto; padding: 2.2rem 1rem 4rem; font-family: var(--sans); }
  .ix-main h1 { font-family: var(--serif); font-size: 2rem; font-weight: 600; margin: 0 0 .4rem; }
  .ix-lede { color: var(--ink2); font-size: 15px; line-height: 1.6; max-width: 40rem; margin: 0 0 2rem; }
  .ix-epreuve { font-size: 11px; font-weight: 700; letter-spacing: .09em; text-transform: uppercase;
                color: var(--ink4); margin: 2.2rem 0 .6rem; }
  .ix-lecon { border-top: 1px solid var(--rule); padding: 1rem 0 .4rem; }
  .ix-lecon h2 { font-family: var(--serif); font-size: 1.15rem; font-weight: 600; line-height: 1.35; margin: 0 0 .5rem; }
  .ix-num { font-family: var(--mono); font-size: .85em; color: var(--accent); margin-right: .35rem; }
  .ix-docs { list-style: none; padding: 0; margin: 0; }
  .ix-docs li { padding: .35rem 0 .7rem; }
  .ix-doc-title { font-size: 15.5px; font-weight: 600; color: var(--ink); text-decoration: none; }
  .ix-doc-title:hover { color: var(--accent); }
  .ix-links { display: flex; flex-wrap: wrap; gap: .3rem .9rem; margin-top: .3rem; font-size: 13px; }
  .ix-links a, .ix-also a { color: var(--accent); text-decoration: none; }
  .ix-also { display: block; margin-top: .25rem; font-size: 12.5px; color: var(--ink3); }
  .ix-others { list-style: none; padding: 0; font-size: 14px; line-height: 1.5; }
  .ix-others li { padding: .45rem 0; border-top: 1px solid var(--rule2); }
  .ix-note { margin-top: 2.5rem; font-size: 12.5px; color: var(--ink3); line-height: 1.6; }
</style>
</head>
<body>
<main class="ix-main">
<h1>Leçons d'agrégation</h1>
<p class="ix-lede">Articles, exercices commentés et développements, rangés par leçon de l'oral de l'agrégation externe de mathématiques. Chaque document se lit ici, composé depuis sa source LaTeX ; le PDF et la source sont à côté.</p>
${alg.length ? `<p class="ix-epreuve">Algèbre et géométrie</p>${alg.map(card).join('')}` : ''}
${ana.length ? `<p class="ix-epreuve">Analyse et probabilités</p>${ana.map(card).join('')}` : ''}
${others ? `<p class="ix-epreuve">Autres leçons servies</p><ul class="ix-others">${others}</ul>` : ''}
${missing.length ? `<p class="ix-note">Non rendus : ${missing.map(escapeHtml).join(', ')}.</p>` : ''}
<p class="ix-note">Numérotation de la liste officielle des leçons, publiée chaque année : à vérifier pour la session préparée.</p>
</main>
</body>
</html>
`;
}

// ---------------------------------------------------------------------------

async function main() {
  const lecons = JSON.parse(await readFile(resolve(ROOT, 'lecons.json'), 'utf8'));
  const known = new Set(lecons.map((l) => l.numero));

  await mkdir(OUT, { recursive: true });
  await rm(resolve(OUT, 'vendor'), { recursive: true, force: true });
  await cp(resolve(ROOT, 'public'), OUT, { recursive: true });
  if (!existsSync(resolve(OUT, 'vendor', 'katex', 'katex.min.js'))) {
    throw new Error('KaTeX absent de public/vendor/katex — lancer npm install');
  }

  const dirs = (await readdir(SOURCE, { withFileTypes: true })).filter((d) => d.isDirectory()).map((d) => d.name).sort();
  const folders = [];
  const refused = [];
  for (const dir of dirs) {
    const numero = /^(\d{3})-/.exec(dir)?.[1];
    if (!numero || !known.has(numero)) {
      refused.push(`${dir} (numéro absent de lecons.json)`);
      continue;
    }
    const files = (await readdir(resolve(SOURCE, dir))).sort();
    const out = resolve(OUT, 'lecons', dir);
    await mkdir(out, { recursive: true });
    const rootRel = `${relative(out, OUT)}/`;
    const crumb = `<a href="${rootRel}index.html#lecon-${numero}">${numero}</a>`;

    const lean = [];
    for (const f of files.filter((x) => x.endsWith('.lean'))) {
      const text = await readFile(resolve(SOURCE, dir, f), 'utf8');
      await copyFile(resolve(SOURCE, dir, f), resolve(out, f));
      await writeFile(resolve(out, `${f}.html`), sourcePage({ text, file: f, rootRel, crumb, links: [], kind: 'Lean' }));
      lean.push({ name: f, href: `lecons/${dir}/${f}.html` });
    }

    const docs = [];
    for (const f of files.filter((x) => x.endsWith('.tex'))) {
      const stem = basename(f, '.tex');
      const tex = await readFile(resolve(SOURCE, dir, f), 'utf8');
      const pdf = existsSync(resolve(out, `${stem}.pdf`));
      const links = [
        ...(pdf ? [[`${stem}.pdf`, 'PDF']] : []),
        [`${f}.html`, 'Source LaTeX'],
        ...lean.map((l) => [`${l.name}.html`, 'Lean']),
      ];
      try {
        const { html, title, macros } = render(tex, `${dir}/${f}`);
        await writeFile(resolve(out, `${stem}.html`),
          readingPage({ title, html, macros, rootRel, crumb, links }));
        await copyFile(resolve(SOURCE, dir, f), resolve(out, f));
        await writeFile(resolve(out, `${f}.html`), sourcePage({
          text: tex, file: f, rootRel, crumb, kind: 'LaTeX',
          links: [[`${stem}.html`, 'Lecture'], ...(pdf ? [[`${stem}.pdf`, 'PDF']] : [])],
        }));
        docs.push({
          title,
          href: `lecons/${dir}/${stem}.html`,
          src: `lecons/${dir}/${f}.html`,
          pdf: pdf ? `lecons/${dir}/${stem}.pdf` : null,
          lean,
          cited: citedLecons(tex).filter((n) => known.has(n)),
        });
        process.stdout.write(`  ✓ ${dir}/${f}\n`);
      } catch (e) {
        refused.push(`${dir}/${f}`);
        process.stderr.write(`  ✗ ${dir}/${f} : ${e.message}\n`);
      }
    }
    if (docs.length) folders.push({ numero, dir, docs });
  }

  await writeFile(resolve(OUT, 'index.html'), indexPage({ lecons, folders, missing: refused }));
  await writeFile(resolve(OUT, '.nojekyll'), '');
  process.stdout.write(`${folders.reduce((n, f) => n + f.docs.length, 0)} documents → dist/\n`);

  // Un fichier refusé fait échouer la commande : c'est le .tex qui sort du
  // sous-ensemble, et c'est lui qu'il faut corriger (ou ce script qu'il faut étendre).
  if (refused.length) {
    process.stderr.write(`${refused.length} refusé(s) : ${refused.join(', ')}\n`);
    process.exit(1);
  }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch((e) => {
    process.stderr.write(`${e.message}\n`);
    process.exit(1);
  });
}
