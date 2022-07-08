import { parser } from './coq-mode.grammar.js';
import { LRLanguage, LanguageSupport, 
         foldNodeProp, foldInside, indentNodeProp } from "@codemirror/language";
import { styleTags, tags as t } from '@lezer/highlight'


let parserWithMetadata = parser.configure({
  props: [
    styleTags({
      Identifier: t.variableName,
      Keyword: t.keyword,
      Vernac: t.atom,
      Tactic: t.keyword,
      Admitter: t.atom,
      Terminator: t.keyword,
      Operator: t.operatorKeyword,
      Boolean: t.bool,
      String: t.string,
      Comment: t.blockComment,
      "( )": t.paren,
      ".": t.separator
    }),
    indentNodeProp.add({
      Application: context => context.column(context.node.from) + context.unit
    }),
    foldNodeProp.add({
      Application: foldInside
    })
  ]
})


export const coqLanguage = LRLanguage.define({
  parser: parserWithMetadata,
  languageData: {
    commentTokens: {line: ";"}
  }
});


export function coqLanguageSupport() {
  return new LanguageSupport(coqLanguage, [])
}
