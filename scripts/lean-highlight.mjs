/**
 * Coloration syntaxique des fichiers Lean 4, pour la vue « source Lean ».
 *
 * Reprise de `site/src/lib/lean.ts` du dépôt learn-lean, à ceci près que la
 * coloration se fait ici à la construction, en HTML statique. Comme là-bas,
 * elle ne prétend pas être exacte : la syntaxe de Lean est extensible, et seul
 * son analyseur saurait distinguer à coup sûr un mot-clé d'un identifiant. On
 * sépare les commentaires, les mots du langage, les tactiques courantes, les
 * chaînes et les nombres, ce qui suffit à suivre une démonstration de l'œil.
 *
 * Les identifiants deviennent des liens dans deux cas : une déclaration du
 * fichier mène à sa ligne, et un nom qui a la forme d'un nom de Mathlib (nom
 * qualifié comme `Nat.dvd_add`, ou `serpent_case` d'au moins deux mots comme
 * `mul_eq_zero`) mène à la recherche de la documentation de Mathlib. Un lien
 * qui tombe à côté arrive sur une page « non trouvé », ce qui se voit.
 */

const MOTS = new Set([
  'theorem', 'lemma', 'def', 'abbrev', 'instance', 'example', 'structure', 'class',
  'namespace', 'end', 'section', 'variable', 'open', 'import', 'noncomputable',
  'private', 'protected', 'partial', 'unsafe', 'attribute', 'deriving', 'where',
  'fun', 'let', 'have', 'show', 'from', 'match', 'with', 'do', 'if', 'then', 'else',
  'by', 'calc', 'this', 'omit', 'in', 'include', 'universe', 'set_option', 'scoped',
])

const TACTIQUES = new Set([
  'intro', 'intros', 'exact', 'apply', 'refine', 'rintro', 'rcases', 'obtain', 'cases',
  'induction', 'simp', 'simpa', 'rw', 'rwa', 'ring', 'ring_nf', 'linarith', 'nlinarith',
  'omega', 'decide', 'norm_num', 'field_simp', 'positivity', 'constructor', 'use',
  'push_cast', 'push_neg', 'linear_combination', 'unfold', 'change', 'convert', 'congr',
  'ext', 'funext', 'abel', 'module', 'gcongr', 'interval_cases', 'fin_cases', 'trivial',
  'rfl', 'sorry', 'nth_rewrite', 'by_contra', 'by_cases', 'subst', 'specialize',
  'exact_mod_cast', 'norm_cast', 'split_ifs', 'filter_upwards', 'contradiction',
  'exfalso', 'left', 'right', 'symm', 'trans', 'calc', 'conv', 'conv_lhs', 'conv_rhs',
])

const MATHLIB = 'https://leanprover-community.github.io/mathlib4_docs/find/?pattern='

const DECL = /^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s:({[]+)/

// Les identifiants de Lean admettent les lettres grecques et les indices ; le
// point sépare les composantes d'un nom qualifié.
const IDENT = /^[A-Za-z_Ͱ-Ͽἀ-῿ℕℤℚℝℂ][A-Za-z0-9_'!?Ͱ-Ͽἀ-῿₀-ₜℕℤℚℝℂ]*(?:\.[A-Za-z_Ͱ-Ͽ][A-Za-z0-9_'!?Ͱ-Ͽ₀-ₜℕℤℚℝℂ]*)*/

const esc = (s) => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
const attr = (s) => esc(s).replace(/"/g, '&quot;')

/** Les déclarations du fichier, par nom complet et par dernier composant. */
function declarations(lines) {
  const out = new Map()
  lines.forEach((l, i) => {
    const m = DECL.exec(l)
    if (!m) return
    const nom = m[1]
    if (!out.has(nom)) out.set(nom, i + 1)
    const court = nom.split('.').pop()
    if (!out.has(court)) out.set(court, i + 1)
  })
  return out
}

function lien(mot, decls) {
  const ligne = decls.get(mot) ?? decls.get(mot.split('.').pop())
  if (ligne && !TACTIQUES.has(mot)) return { href: `#L${ligne}`, cls: 'lean-ref' }
  const qualifie = /^[A-Z][A-Za-z0-9]*(\.[A-Za-z_][A-Za-z0-9_']*)+$/.test(mot)
  const serpent = /^[a-z][a-z0-9]*(_[a-z0-9']+){1,}$/.test(mot)
  if (qualifie || serpent) return { href: `${MATHLIB}${encodeURIComponent(mot)}#doc`, cls: 'lean-lib' }
  return null
}

const span = (cls, s) => `<span class="${cls}">${esc(s)}</span>`

/** Une ligne hors commentaire de bloc, en HTML. */
function ligneHtml(ligne, decls) {
  let out = ''
  let i = 0
  while (i < ligne.length) {
    const reste = ligne.slice(i)
    if (reste.startsWith('--')) { out += span('lean-com', reste); break }
    const chaine = /^"(?:[^"\\]|\\.)*"/.exec(reste)
    if (chaine) { out += span('lean-str', chaine[0]); i += chaine[0].length; continue }
    const mot = IDENT.exec(reste)
    if (mot) {
      const m = mot[0]
      const nu = m.split('.').pop()
      if (MOTS.has(m)) out += span('lean-kw', m)
      else if (TACTIQUES.has(nu) && !decls.has(m)) out += span('lean-tac', m)
      else {
        const l = lien(m, decls)
        out += l ? `<a class="${l.cls}" href="${attr(l.href)}"${l.cls === 'lean-lib' ? ' target="_blank" rel="noopener"' : ''}>${esc(m)}</a>` : esc(m)
      }
      i += m.length
      continue
    }
    const nombre = /^\d+/.exec(reste)
    if (nombre) { out += span('lean-num', nombre[0]); i += nombre[0].length; continue }
    out += esc(ligne[i])
    i++
  }
  return out
}

/**
 * Le fichier entier, une ligne par élément, numérotée et ancrée (`#L12`). Les
 * commentaires de bloc `/- … -/`, docstrings comprises, traversent les lignes :
 * on garde leur état d'une ligne à l'autre, et on suit leur imbrication.
 */
export function highlightLean(source) {
  const lines = source.replace(/\n$/, '').split('\n')
  const decls = declarations(lines)
  let depth = 0
  return lines.map((ligne, k) => {
    let html = ''
    let i = 0
    while (i < ligne.length) {
      if (depth > 0) {
        // Dans un commentaire : avancer jusqu'à sa fermeture.
        let j = i
        while (j < ligne.length && depth > 0) {
          if (ligne.startsWith('/-', j)) { depth++; j += 2 }
          else if (ligne.startsWith('-/', j)) { depth--; j += 2 }
          else j++
        }
        html += span('lean-com', ligne.slice(i, j))
        i = j
        continue
      }
      const debut = ligne.indexOf('/-', i)
      const tiret = ligne.indexOf('--', i)
      if (debut === -1 || (tiret !== -1 && tiret < debut)) { html += ligneHtml(ligne.slice(i), decls); break }
      html += ligneHtml(ligne.slice(i, debut), decls)
      depth = 1
      let j = debut + 2
      while (j < ligne.length && depth > 0) {
        if (ligne.startsWith('/-', j)) { depth++; j += 2 }
        else if (ligne.startsWith('-/', j)) { depth--; j += 2 }
        else j++
      }
      html += span('lean-com', ligne.slice(debut, j))
      i = j
    }
    const n = k + 1
    // Chaque ligne est un bloc : pas de saut de ligne entre elles, sinon le
    // <pre> en ajouterait un second. Une ligne vide garde sa hauteur.
    return `<span class="lean-line" id="L${n}"><a class="lean-ln" href="#L${n}">${n}</a>${html || ' '}</span>`
  }).join('')
}

export const LEAN_STYLE = `
  pre.lean { white-space: pre; overflow-x: auto; word-break: normal; }
  .lean-line { display: block; padding-right: 1rem; }
  .lean-line:target { background: #fdf6dc; }
  .lean-ln { display: inline-block; width: 4ch; margin-right: 1.4ch; text-align: right;
             color: var(--ink4); text-decoration: none; user-select: none; }
  .lean-ln:hover { color: var(--accent); }
  .lean-kw { color: var(--accent); font-weight: 600; }
  .lean-tac { color: #0e6744; }
  .lean-com { color: var(--ink3); font-style: italic; }
  .lean-str { color: #9c6d06; }
  .lean-num { color: #8a3b1e; }
  .lean-ref, .lean-lib { color: inherit; text-decoration: none; }
  .lean-ref { color: var(--accent); }
  .lean-ref:hover, .lean-lib:hover { text-decoration: underline dotted; text-underline-offset: 2px; }
`
