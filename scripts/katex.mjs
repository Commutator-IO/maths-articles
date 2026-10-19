#!/usr/bin/env node
/**
 * Copie KaTeX de `node_modules` dans `public/vendor/katex/` (repris de
 * grothendieck-project).
 *
 * Les vues de lecture sont des pages statiques, servies telles quelles : elles
 * chargent KaTeX depuis le site plutôt que depuis un CDN, ce qui les garde
 * lisibles hors ligne. Seules les polices WOFF2 sont copiées, les deux autres
 * formats ne servant à aucun navigateur actuel.
 */

import { cp, mkdir, readdir } from 'node:fs/promises';
import { resolve } from 'node:path';

const RACINE = resolve(import.meta.dirname, '..');
const SOURCE = resolve(RACINE, 'node_modules', 'katex', 'dist');
const CIBLE = resolve(RACINE, 'public', 'vendor', 'katex');

async function principal() {
  await mkdir(resolve(CIBLE, 'fonts'), { recursive: true });

  for (const f of ['katex.min.css', 'katex.min.js']) {
    await cp(resolve(SOURCE, f), resolve(CIBLE, f));
  }
  await cp(
    resolve(SOURCE, 'contrib', 'auto-render.min.js'),
    resolve(CIBLE, 'auto-render.min.js'),
  );

  const polices = (await readdir(resolve(SOURCE, 'fonts'))).filter((f) => f.endsWith('.woff2'));
  for (const f of polices) {
    await cp(resolve(SOURCE, 'fonts', f), resolve(CIBLE, 'fonts', f));
  }

  process.stdout.write(`KaTeX + ${polices.length} polices → public/vendor/katex/\n`);
}

principal().catch((e) => {
  process.stderr.write(`${e.message}\n`);
  process.exit(1);
});
