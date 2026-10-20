#!/usr/bin/env node
/**
 * Compile les `tikzpicture` des fiches en SVG, pour les vues web.
 *
 *   npm run tikz             chaque figure qui n'a pas encore de SVG
 *   npm run tikz -- --check  échoue s'il en manque un, sans rien compiler
 *
 * Repris de grothendieck-project. KaTeX ne sait pas dessiner une figure TikZ,
 * et TikZ n'a pas d'autre moteur que TeX : chaque figure est donc compilée une
 * fois, seule, dans un document `standalone` qui lit le même réglage que les
 * PDF (`lecons/figures/tikz-setup.tex`), puis convertie en SVG par pdftocairo
 * (poppler).
 *
 * Les SVG sont versionnés, dans `lecons/figures/`, et nommés par une empreinte
 * de la source de la figure. Le site se construit donc sans TeX, et une figure
 * périmée est impossible : qu'une coordonnée change, le nom change, render.mjs
 * ne trouve plus le SVG et s'arrête en donnant la commande à lancer. Un SVG
 * qu'aucune figure ne nomme plus est supprimé.
 */

import { execFile } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync } from 'node:fs';
import { mkdir, mkdtemp, readdir, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { promisify } from 'node:util';

const exec = promisify(execFile);

const ROOT = resolve(import.meta.dirname, '..');
const SOURCE = resolve(ROOT, 'lecons');
export const FIGURES = resolve(SOURCE, 'figures');

export const PICTURE = /\\begin\{tikzpicture\}[\s\S]*?\\end\{tikzpicture\}/g;

/** Commentaires retirés et espaces réduits : une figure réindentée dessine la même chose. */
export function pictureHash(raw) {
  const drawn = raw.replace(/(?<!\\)%.*$/gm, '').replace(/\s+/g, ' ').trim();
  return createHash('sha256').update(drawn).digest('hex').slice(0, 12);
}

async function pictures() {
  const out = new Map();
  for (const dir of await readdir(SOURCE, { withFileTypes: true })) {
    if (!dir.isDirectory() || dir.name === 'figures') continue;
    for (const file of await readdir(resolve(SOURCE, dir.name))) {
      if (!file.endsWith('.tex')) continue;
      const tex = await readFile(resolve(SOURCE, dir.name, file), 'utf8');
      for (const m of tex.matchAll(PICTURE)) {
        out.set(pictureHash(m[0]), { raw: m[0], where: `${dir.name}/${file}` });
      }
    }
  }
  return out;
}

const standalone = (raw) => `\\documentclass[tikz,border=3pt]{standalone}
\\usepackage{amsmath,amssymb}
\\usepackage{fontspec}
\\input{${join(FIGURES, 'tikz-setup.tex')}}
\\begin{document}
${raw}
\\end{document}
`;

async function compile(hash, raw) {
  const work = await mkdtemp(join(tmpdir(), 'tikz-'));
  try {
    await writeFile(join(work, 'p.tex'), standalone(raw));
    await exec('tectonic', ['-X', 'compile', join(work, 'p.tex'), '--outdir', work]);
    await exec('pdftocairo', ['-svg', join(work, 'p.pdf'), join(FIGURES, `${hash}.svg`)]);
  } finally {
    await rm(work, { recursive: true, force: true });
  }
}

async function main() {
  const check = process.argv.includes('--check');
  await mkdir(FIGURES, { recursive: true });
  const all = await pictures();
  const missing = [...all].filter(([h]) => !existsSync(resolve(FIGURES, `${h}.svg`)));

  if (check) {
    if (missing.length) {
      for (const [h, p] of missing) process.stderr.write(`  pas de SVG pour ${h} (${p.where})\n`);
      process.stderr.write('Lancer `npm run tikz`.\n');
      process.exit(1);
    }
  } else {
    for (const [h, p] of missing) {
      try {
        await compile(h, p.raw);
        process.stdout.write(`  ${h}.svg  ${p.where}\n`);
      } catch (e) {
        process.stderr.write(`tikz : ${p.where} : la figure ${h} ne compile pas\n${e.stdout ?? ''}${e.stderr ?? e.message}\n`);
        process.exit(1);
      }
    }
    for (const f of await readdir(FIGURES)) {
      if (f.endsWith('.svg') && !all.has(f.slice(0, -4))) {
        await rm(resolve(FIGURES, f));
        process.stdout.write(`  ${f} supprimé : aucune figure ne le nomme plus\n`);
      }
    }
  }
  process.stdout.write(`${all.size} figure(s), ${check ? 0 : missing.length} compilée(s) → lecons/figures/\n`);
}

if (import.meta.url === pathToFileURL(process.argv[1] ?? '').href) await main();
