import { ExternalTokenizer } from '@lezer/lr';
import * as terms from './coq-mode.grammar.terms';

const DOT = '.'.codePointAt(0),
      [LPAREN, ASTK, RPAREN] = ['(', '*', ')'].map(s => s.codePointAt(0)),
      WS = [' ', '\t', '\r', '\n'].map(s => s.codePointAt(0)),
      WS_OR_EOF = [...WS, -1];

export const endOfSentence = new ExternalTokenizer((stream, stack) => {
    if (stream.peek(0) == DOT && WS_OR_EOF.includes(stream.peek(1))) {
        stream.advance(1);
        stream.acceptToken(terms.endOfSentence);
    }
});

export const commentFragment = new ExternalTokenizer((stream, stack) => {
    let adv = false;
    while (stream.peek(0) != -1 &&
           /* this is ridiculous */
           !(stream.peek(0) == LPAREN && stream.peek(1) == ASTK ||
             stream.peek(0) == ASTK && stream.peek(1) == RPAREN)) {
        stream.advance(1);
        adv = true;
    }
    if (adv) stream.acceptToken(terms.commentFragment);
});

export function specializeIdent(tok: string) {
    return kwdict.get(tok) ?? -1;
}


const vernacular = [
    'Abort', 'About', 'Add', 'All', 'Arguments', 'Asymmetric', 'Axiom',
    'Bind',
    'Canonical', 'Check', 'Class', 'Close', 'Coercion', 'CoFixpoint', 'Comments',
    'CoInductive', 'Compute', 'Context', 'Constructors', 'Contextual', 'Corollary',
    'Defined', 'Definition', 'Delimit',
    'Fail',
    'Eval',
    'End', 'Example', 'Export', 'Extraction',
    'Fact', 'Fixpoint', 'From',
    'Global', 'Goal', 'Graph',
    'Hint', 'Hypotheses', 'Hypothesis',
    'Implicit', 'Implicits', 'Import', 'Inductive', 'Infix', 'Instance',
    'Lemma', 'Let', 'Local', 'Ltac',
    'Module', 'Morphism',
    'Next', 'Notation',
    'Obligation', 'Open',
    'Parameter', 'Parameters', 'Prenex', 'Print', 'Printing', 'Program',
    'Patterns', 'Projections', 'Proof',
    'Proposition',
    'Qed',
    'Record', 'Relation', 'Remark', 'Require', 'Reserved', 'Resolve', 'Rewrite',
    'Save', 'Scope', 'Search', 'SearchAbout', 'Section', 'Set', 'Show', 'Strict', 'Structure',
    'Tactic', 'Time', 'Theorem', 'Types',
    'Unset',
    'Variable', 'Variables', 'View'
  ];

  const gallina = [
    'as',
    'at',
    'cofix', 'crush',
    'else', 'end',
    'False', 'fix', 'for', 'forall', 'fun',
    'if', 'in', 'is',
    'let',
    'match',
    'of',
    'Prop',
    'return',
    'struct',
    'then', 'True', 'Type',
    'when', 'with'
  ];

  const tactics = [
    'after', 'apply', 'assert', 'auto', 'autorewrite',
    'case', 'change', 'clear', 'compute', 'congruence', 'constructor',
    'congr', 'cut', 'cutrewrite',
    'dependent', 'destruct',
    'eapply', 'eauto', 'ecase', 'econstructor', 'edestruct',
    'ediscriminate', 'eelim', 'eenough', 'eexists', 'eexact', 'einduction',
    'einjection', 'eleft', 'epose', 'eright', 'esplit',
    'elim', 'enough', 'exists',
    'field', 'firstorder', 'fold', 'fourier',
    'generalize',
    'have', 'hnf',
    'induction', 'injection', 'instantiate', 'intro', 'intros', 'inversion',
    'left',
    'move',
    'pattern', 'pose',
    'refine', 'remember', 'rename', 'repeat', 'replace', 'revert', 'rewrite',
    'right', 'ring',
    'set', 'simpl', 'specialize', 'split', 'subst', 'suff', 'symmetry',
    'transitivity', 'trivial', 'try',
    'unfold', 'unlock', 'using',
    'vm_compute',
    'where', 'wlog'
  ];

  const terminators = [
    'assumption',
    'eassumption',
    'by',
    'contradiction',
    'discriminate',
    'easy',
    'exact',
    'now',
    'lia',
    'omega',
    'reflexivity',
    'tauto'
  ];

  const admitters = [
    'admit',
    'Admitted'
  ];

  const kwdict = new Map([].concat(
    vernacular.map(k => [k, terms.Vernac]),
    tactics.map(k => [k, terms.Tactic]),
    gallina.map(k => [k, terms.Keyword]),
    terminators.map(k => [k, terms.Terminator]), 
    admitters.map(k => [k, terms.Admitter])));


  export { vernacular, gallina, tactics, terminators, admitters }