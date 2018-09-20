/*
 * ACSL language grammar based on official specification 1.13.
 * Meant for use with ANTLR.
 * Copyright belongs to original authors.
 *
 * Built up by Maxim Menshchikov.
 *
 * This work is licensed under the Creative Commons Attribution 4.0
 * International License. To view a copy of this license,
 * visit http://creativecommons.org/licenses/by/4.0/ or send a letter
 * to Creative Commons, PO Box 1866, Mountain View, CA 94042, USA.
 */
grammar ACSL;

import C;

// Edit to get rid of dependency upon ANTLR C++ target.
@parser::preinclude {
    #include "CParser.h"
}

// own additions --- start
@lexer::members {
  bool skipCommentSymbols;
}
// own additions --- end

id
    : Identifier
    ;
string
    : StringLiteral+
    ;

// term.tex
literal
    :   '\\true' | '\\false'
    |   Constant
    // let's use C classes
    ;

bin_op
    : '+' | '-' | '*' | '/' | '%' | '<<' | '>>'
    | '==' | '!=' | '<=' | '>=' | '>' | '<'
    | '&&' | '||' | '^^'
    | '&' | '|' | '-->' | '<-->' | '^'
    ;

unary_op
    : '+' | '-'
    | '!'
    | '-'
    | '*'
    | '&'
    ;

term
    : literal
    | poly_id
    | unary_op
    | term bin_op term
    | term '[' term ']'
    | '{' term '\\with' '[' term ']' '=' term '}'
    | term '.' id
    | '{' term '\\with' '.' id '=' term '}'
    | term '->' id
    | '(' type_expr ')' term
    | poly_id '(' term (',' term)* ')'
    | '(' term ')'
    | term '?' term ':' term
    | '\\let' id '=' term ';' term
    | 'sizeof' '(' term ')'
    | 'sizeof' '(' typeName ')'
    | id ':' term
    | string ':' term
// oldandresult.tex
    | '\\old' '(' term ')'
    | '\\result'
// memory.tex:
    | '\\null'
    | '\\base_addr' one_label? '(' term ')'
    | '\\block_length' one_label? '(' term ')'
    | '\\offset' one_label?  '(' term ')'
    | '{' '\\allocation' '}' one_label?   '(' term ')'
// exitbehavior.tex
    | '\\exit_status'
// at.tex
    | '\\at' '(' term ',' label_id ')'
    ;

poly_id
    : Identifier
    ;

// predicate.tex
rel_op
    : '==' | '!=' | '<=' | '>=' | '>' | '<'
    ;
pred
    : '\\true' | '\\false'
    | term (rel_op term)+
    | ident '(' term (',' term)* ')'
    | '(' pred ')'
    | pred '&&' pred
    | pred '||' pred
    | pred '==>' pred
    | pred '<==>' pred
    | '!' pred
    | pred '^^' pred
    | term '?' pred ':' pred
    | pred '?' pred ':' pred
    | '\\let' id '=' term ';' pred
    | '\\let' id '=' pred ';' pred
    | '\\forall' binders ';' pred
    | id ':' pred
    | string ':' pred
// oldandresult.tex
    | '\\old' '(' pred ')'
// loc.tex
    | '\\subset' '(' tset ',' tset ')'
    | term '\\in' tset
// memory.tex:
    | '\\allocable' one_label? '(' term ')'
    | '\\freeable' one_label? '(' term ')'
    | '\\fresh'   two_labels? '(' term ',' term ')'
    | '\\valid'  one_label?  '(' location_address ')'
    | '\\valid_read'  one_label? '(' location_address ')'
    | '\\separated' '(' location_address ',' location_addresses ')'
    ;

ident
    : id
    ;

// binders.tex
binders
    : binder (',' binder)*
    ;

binder
    : type_expr variable_ident (',' variable_ident)*
    ;

type_expr
    : logic_type_expr | typeName
    ;

logic_type_expr
    : built_in_logic_type | id
    ;

built_in_logic_type
    : 'boolean' | 'integer' | 'real'
    ;

variable_ident
    : id
    | '*' variable_ident
    | variable_ident '[]'
    | '(' variable_ident ')'
    ;

// fn_behavior.tex
function_contract
    : requires_clause* terminates_clause? decreases_clause? simple_clause* named_behavior* completeness_clause*
    ;

requires_clause
    : 'requires' pred ';'
    ;

terminates_clause
    : 'terminates' pred ';'
    ;

decreases_clause
    : 'decreases' term ('for' id)? ';'
    ;

simple_clause
    : assigns_clause | ensures_clause
    | allocation_clause | abrupt_clause
    ;

assigns_clause
    : 'assigns' locations ';'
    ;

locations
    : location (',' location)* | '\\nothing'
    ;

location
    : tset
    ;

ensures_clause
    : 'ensures' pred ';'
    ;

named_behavior
    : 'behavior' id ':' behavior_body
    ;

behavior_body
    : assumes_clause* requires_clause* simple_clause*
    ;

assumes_clause
    : 'assumes' pred ';'
    ;

completeness_clause
    : 'complete' 'behaviors' (id ',' (',' id)*)? ';'
    | 'disjoint' 'behaviors' (id ',' (',' id)*)? ';'
    ;

// loc.tex
tset
    : '\\empty'
    | tset '->' id
    | tset '.' id
    | '*' tset
    | '&' tset
    | tset '[' tset ']'
    | term? '..' term?
    | '\\union' ( tset (',' tset)* )
    | '\\inter' ( tset (',' tset)* )
    | tset '+' tset
    | '(' tset ')'
    | '{' tset '|' binders (':' pred)? '}'
    | '{' (tset (',' tset)*)? '}'
    | term
    ;

c_compound_statement
    : '{' declaration* statement* assertion+ '}'
    ;

c_statement
    : assertion c_statement
    ;

assertion
    : '/*@' 'assert' pred ';' '*/'
    | '/*@' 'for' id (',' id)* ':' 'assert' pred ';' '*/'
    ;


// allocation.tex
allocation_clause
    : 'allocates' dyn_allocation_addresses ';'
    | 'frees' dyn_allocation_addresses ';'
    ;

loop_allocation
    : 'loop' 'allocates' dyn_allocation_addresses ';'
    | 'loop' 'frees'  dyn_allocation_addresses ';'
    ;

dyn_allocation_addresses
    : location_addresses
    | '\\nothing'
    ;

// memory.tex
one_label
    : '{' label_id '}'
    ;

two_labels
    : '{' label_id ',' label_id '}'
    ;

location_addresses
    : location_address (',' location_address)*
    ;

location_address
    : tset
    ;

// exitbehaviour.tex
abrupt_clause
    : exits_clause
    ;

exits_clause
    : 'exits' pred ';'
    ;

abrupt_clause_stmt
    : breaks_clause | continues_clause | returns_clause
    ;

breaks_clause
    : 'breaks' pred ';'
    ;

continues_clause
    : 'continues' pred ';'
    ;

returns_clause
    : 'returns' pred ';'
    ;

// at.tex
label_id
    : 'Here' | 'Old' | 'Pre' | 'Post'
    | 'LoopEntry' | 'LoopCurrent' | 'Init'
    | id
    ;

// own additions --- start
AcslCommentStart
    : '/*@' {skipCommentSymbols = true;}
    ;

AcslCommentEnd
    : '@*/' {skipCommentSymbols = false;}
    ;

AcslCommentIntermediate
    : '@' { if (skipCommentSymbols) skip(); }
    ;

acsl_comment
    : AcslCommentStart Newline* function_contract AcslCommentEnd Newline*
    ;
// own additions --- end