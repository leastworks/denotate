// One document is one program. Keep names on the word token so reserved words
// cannot slip through a second, context-specific identifier regex.
module.exports = grammar({
  name: 'inputmapping',
  extras: $ => [/[ \t\r\n]+/, $.comment],
  word: $ => $.identifier,
  reserved: {
    global: $ => ['input', 'slot', 'when', 'available', 'present', 'and', 'or', 'not']
  },
  rules: {
    source_file: $ => seq(optional('\uFEFF'), repeat(choice($.declaration, $.mapping))),
    declaration: $ => seq(
      field('kind', choice('input', 'slot')),
      field('name', $.identifier), repeat(seq(',', field('name', $.identifier))), ';'
    ),
    mapping: $ => seq(
      field('target', $.identifier), '<-', field('input', $.identifier),
      optional(seq('when', field('condition', $._expression))), ';'
    ),
    _expression: $ => choice($.available, $.present, $.and, $.or, $.not, $.group),
    available: $ => seq('available', '(', field('argument', $.identifier), ')'),
    present: $ => seq('present', '(', field('argument', $.identifier), ')'),
    and: $ => prec.left(2, seq(field('left', $._expression), 'and', field('right', $._expression))),
    or: $ => prec.left(1, seq(field('left', $._expression), 'or', field('right', $._expression))),
    not: $ => prec(3, seq(field('keyword', 'not'), field('operand', $._expression))),
    group: $ => seq('(', field('inner', $._expression), ')'),
    identifier: _ => /[a-z][A-Za-z0-9_]*/,
    comment: _ => token(seq('//', /[^\r\n]*/))
  }
});
