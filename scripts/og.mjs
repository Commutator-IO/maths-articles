#!/usr/bin/env node
/**
 * Compile les images d'aperçu (Open Graph) des fiches, pour les partages sur
 * LinkedIn, Mastodon, Slack…
 *
 *   npm run og             chaque image qui n'existe pas encore
 *   npm run og -- --check  échoue s'il en manque une, sans rien compiler
 *
 * Même principe que tikz.mjs : l'image de chaque fiche est une page TikZ de
 * 1200 × 630 px (titre, sous-titre, leçon et première figure de la fiche),
 * compilée par Tectonic puis convertie en PNG par pdftocairo. Les PNG sont
 * versionnés dans `lecons/figures/og/` et nommés par une empreinte de leur
 * source : qu'un titre change, render.mjs ne trouve plus l'image et s'arrête
 * en donnant la commande à lancer. Une image qu'aucune fiche ne nomme plus est
 * supprimée.
 */

import { execFile } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync } from 'node:fs';
import { mkdir, mkdtemp, readdir, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { promisify } from 'node:util';
import { FIGURES, PICTURE } from './tikz.mjs';

const exec = promisify(execFile);

const ROOT = resolve(import.meta.dirname, '..');
const SOURCE = resolve(ROOT, 'lecons');
export const OG = resolve(FIGURES, 'og');
export const OG_WIDTH = 1200;
export const OG_HEIGHT = 630;

/** Le contenu du groupe `{…}` qui commence à `i` (accolades équilibrées). */
function group(s, i) {
  while (/\s/.test(s[i])) i++;
  if (s[i] !== '{') return null;
  let depth = 0;
  for (let j = i; j < s.length; j++) {
    if (s[j] === '\\') { j++; continue; }
    if (s[j] === '{') depth++;
    else if (s[j] === '}' && --depth === 0) return s.slice(i + 1, j);
  }
  return null;
}

/** L'intitulé court d'une leçon : ce qui précède le premier « : » ou le premier point. */
function shortIntitule(intitule) {
  return intitule.split(/\s:\s|\.\s|\.$/)[0].trim().replace(/[ℕℤℚℝℂ][ⁿ²³]?/g, (m) =>
    `$\\mathbb{${'NZQRC'['ℕℤℚℝℂ'.indexOf(m[0])]}}${m[1] ? `^{${{ 'ⁿ': 'n', '²': '2', '³': '3' }[m[1]]}}` : ''}$`);
}

function body({ title, subtitle, kicker, macros, picture }) {
  const width = picture ? 10.9 : 16.6;
  // Un titre long passe en plus petit, pour ne pas déborder sur la figure.
  const size = title.replace(/\\[a-zA-Z]+|[{}$]/g, '').length > 45 ? '{24}{30}' : '{30}{37}';
  // Espace insécable devant les deux-points, à la française.
  [title, subtitle, kicker] = [title, subtitle, kicker].map((x) => x.replace(/ :/g, '~:'));
  return `\\documentclass[border=0pt]{standalone}
\\usepackage{amsmath,amssymb}
\\usepackage{tikz}
\\usepackage{fontspec}
\\usepackage{adjustbox}
\\input{tikz-setup.tex}
${macros}
\\hyphenpenalty=10000 \\exhyphenpenalty=10000
\\begin{document}
${picture ? `\\sbox0{${picture}}` : ''}
\\begin{tikzpicture}
\\useasboundingbox[fill=white] (0,0) rectangle (20,10.5);
\\fill[accent] (0,0) rectangle (0.3,10.5);
\\node[anchor=north west,inner sep=0,font=\\sffamily\\large,text=accent] (k) at (1.3,9.5) {${kicker}};
\\node[anchor=north west,inner sep=0,text width=${width}cm,align=left,font=\\fontsize${size}\\selectfont\\bfseries] (t) at ([yshift=-0.7cm]k.south west) {${title}};
${subtitle ? `\\node[anchor=north west,inner sep=0,text width=${width}cm,align=left,font=\\fontsize{17}{22}\\selectfont,text=black!65] at ([yshift=-0.55cm]t.south west) {${subtitle}};` : ''}
\\node[anchor=south west,inner sep=0,font=\\sffamily,text=black!60] at (1.3,0.9) {Michel Hua\\quad·\\quad agreg.commutator.io};
${picture ? '\\node at (16.1,5.25) {\\adjustbox{max width=6.2cm,max height=7.4cm}{\\usebox0}};' : ''}
\\end{tikzpicture}
\\end{document}
`;
}

/**
 * La carte d'une fiche : `{ hash, source }`. `intitule` est celui de la leçon
 * dans lecons.json. Sans `tex`, la carte de la page d'accueil.
 */
export function cardFor({ tex, numero, intitule } = {}) {
  let spec;
  if (!tex) {
    spec = {
      kicker: 'AGRÉGATION EXTERNE DE MATHÉMATIQUES',
      title: 'Leçons d\'agrégation',
      subtitle: 'Des fiches de cours rigoureuses, illustrées en TikZ, et leurs preuves vérifiées en Lean avec Mathlib.',
      macros: '',
      picture: null,
    };
  } else {
    const pre = tex.slice(0, tex.indexOf('\\begin{document}')).replace(/(?<!\\)%.*$/gm, '');
    const raw = group(pre, pre.indexOf('\\title') + '\\title'.length) ?? '';
    // Le sous-titre est la dernière ligne s'il est composé en \large ; les autres sont le titre.
    const parts = raw.split(/\\\\(?:\[[^\]]*\])?/);
    const hasSub = parts.length > 1 && /\\(large|Large)\b/.test(parts.at(-1));
    const title = (hasSub ? parts.slice(0, -1) : parts).join(' ');
    const subtitle = hasSub ? parts.at(-1) : '';
    const macros = pre.split('\n')
      .filter((l) => /^\s*\\(newcommand|DeclareMathOperator)/.test(l)).join('\n');
    const picture = tex.slice(tex.indexOf('\\begin{document}')).match(PICTURE)?.[0] ?? null;
    spec = {
      kicker: `LEÇON ${numero}\\quad·\\quad ${shortIntitule(intitule)}`,
      title: title.trim(),
      subtitle: subtitle.replace(/\\(large|Large|small|normalsize)\b/g, '').trim(),
      macros,
      picture,
    };
  }
  const source = body(spec);
  const hash = createHash('sha256').update(source).digest('hex').slice(0, 12);
  return { hash, source };
}

async function cards() {
  const lecons = JSON.parse(await readFile(resolve(ROOT, 'lecons.json'), 'utf8'));
  const byNum = Object.fromEntries(lecons.map((l) => [l.numero, l.intitule]));
  const out = new Map();
  const site = cardFor();
  out.set(site.hash, { ...site, where: 'index.html' });
  for (const dir of await readdir(SOURCE, { withFileTypes: true })) {
    const numero = /^(\d{3})-/.exec(dir.name)?.[1];
    if (!dir.isDirectory() || !byNum[numero]) continue;
    for (const file of await readdir(resolve(SOURCE, dir.name))) {
      if (!file.endsWith('.tex')) continue;
      const tex = await readFile(resolve(SOURCE, dir.name, file), 'utf8');
      const card = cardFor({ tex, numero, intitule: byNum[numero] });
      out.set(card.hash, { ...card, where: `${dir.name}/${file}` });
    }
  }
  return out;
}

async function compile(hash, source) {
  const work = await mkdtemp(join(tmpdir(), 'og-'));
  try {
    await writeFile(join(work, 'card.tex'), source);
    await writeFile(join(work, 'tikz-setup.tex'), await readFile(join(FIGURES, 'tikz-setup.tex')));
    await exec('tectonic', ['-X', 'compile', join(work, 'card.tex'), '--outdir', work]);
    await exec('pdftocairo', ['-png', '-singlefile', '-scale-to-x', `${OG_WIDTH}`,
      '-scale-to-y', `${OG_HEIGHT}`, join(work, 'card.pdf'), join(OG, hash)]);
  } finally {
    await rm(work, { recursive: true, force: true });
  }
}

async function main() {
  const check = process.argv.includes('--check');
  await mkdir(OG, { recursive: true });
  const all = await cards();
  const missing = [...all].filter(([h]) => !existsSync(resolve(OG, `${h}.png`)));

  if (check) {
    if (missing.length) {
      for (const [h, c] of missing) process.stderr.write(`  pas d'image d'aperçu ${h} (${c.where})\n`);
      process.stderr.write('Lancer `npm run og`.\n');
      process.exit(1);
    }
  } else {
    for (const [h, c] of missing) {
      try {
        await compile(h, c.source);
        process.stdout.write(`  ${h}.png  ${c.where}\n`);
      } catch (e) {
        process.stderr.write(`og : ${c.where} : l'image ${h} ne compile pas\n${e.stdout ?? ''}${e.stderr ?? e.message}\n`);
        process.exit(1);
      }
    }
    for (const f of await readdir(OG)) {
      if (f.endsWith('.png') && !all.has(f.slice(0, -4))) {
        await rm(resolve(OG, f));
        process.stdout.write(`  ${f} supprimé : aucune fiche ne le nomme plus\n`);
      }
    }
  }
  process.stdout.write(`${all.size} image(s) d'aperçu, ${check ? 0 : missing.length} compilée(s) → lecons/figures/og/\n`);
}

if (import.meta.url === pathToFileURL(process.argv[1] ?? '').href) await main();
