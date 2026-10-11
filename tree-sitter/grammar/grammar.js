// Same base language as the shared fixture manifest. No zero-arity extension.
module.exports = grammar({
  name: 'denotate',
  extras: $ => [/[ \t\r\n]+/, $.comment],
  word: $ => $.identifier,
  reserved: { global: $ => ['module', 'use', 'sort', 'const', 'relation', 'input'] },
  rules: {
    source_file: $ => seq(optional('\uFEFF'), $.module, repeat($._declaration)),
    module: $ => seq('module', field('name', $.identifier), ';'),
    _declaration: $ => choice($.import, $.sort, $.constants, $.relation, $.statement),
    import: $ => seq('use', field('name', $.identifier), ';'),
    sort: $ => seq('sort', field('name', $.identifier), ';'),
    constants: $ => seq('const', field('name', $.constant), repeat(seq(',', field('name', $.constant))), ':', field('sort', $.identifier), ';'),
    relation: $ => seq(field('kind', choice('relation', 'input')), field('name', $.identifier), '(', $.parameter, repeat(seq(',', $.parameter)), ')', ';'),
    parameter: $ => seq(field('name', $.identifier), ':', field('sort', $.identifier)),
    statement: $ => seq(field('head', $.atom), optional(seq(':-', $._literal, repeat(seq(',', $._literal)))), ';'),
    _literal: $ => choice($.positive_atom, $.negative_atom),
    negative_atom: $ => seq('!', $.atom),
    atom: $ => seq(field('name', $.identifier), '(', $._named_term, repeat(seq(',', $._named_term)), ')'),
    positive_atom: $ => seq(field('name', $.identifier), '(', $._term, repeat(seq(',', $._term)), ')'),
    _term: $ => choice($._named_term, $.anonymous),
    _named_term: $ => choice($.variable, $.constant),
    anonymous: _ => '_',
    identifier: _ => /[A-Za-z][A-Za-z0-9_]*/,
    constant: _ => /[a-z][A-Za-z0-9_]*/,
    variable: _ => /[A-Z][A-Za-z0-9_]*/,
    comment: _ => token(seq('//', /[^\r\n]*/))
  }
});
