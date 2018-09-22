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
    : '\\true'                                          # true_constant
    | '\\false'                                         # false_constant
    // let's use C classes
    | Constant                                          # trivial_constant
    | string                                            # string_constant
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
    : literal                                           # literal_term
    | poly_id                                           # variable_term
    | unary_op term                                     # unary_op_term
    | term bin_op term                                  # binary_op_term
    | term '[' term ']'                                 # array_access_term
    | '{' term '\\with' '[' term ']' '=' term '}'       # array_func_modifier_term
    | term '.' id                                       # structure_field_access_term
    | '{' term '\\with' '.' id '=' term '}'             # field_func_modifier_term
    | term '->' id                                      # pointer_structure_field_access_term
    | '(' type_expr ')' term                            # cast_term
    | poly_id '(' term (',' term)* ')'                  # func_application_term
    | '(' term ')'                                      # parentheses_term
    | term '?' term ':' term                            # ternary_cond_term
    | '\\let' id '=' term ';' term                      # local_binding_term
    | 'sizeof' '(' term ')'                             # sizeof_term
    | 'sizeof' '(' typeName ')'                         # sizeof_type_term
    | id ':' term                                       # syntactic_naming_term
    | string ':' term                                   # syntactic_naming_term
// oldandresult.tex
    | '\\old' '(' term ')'                              # old_term
    | '\\result'                                        # result_term
// memory.tex:
    | '\\null'                                          # null_term
    | '\\base_addr' one_label? '(' term ')'             # base_addr_term
    | '\\block_length' one_label? '(' term ')'          # block_length_term
    | '\\offset' one_label?  '(' term ')'               # offset_term
    | '{' '\\allocation' '}' one_label?   '(' term ')'  # allocation_term
// exitbehavior.tex
    | '\\exit_status'                                   # exit_status_term
// at.tex
    | '\\at' '(' term ',' label_id ')'                  # at_term
    ;

poly_id
    : Identifier
    ;

// predicate.tex
rel_op
    : '==' | '!=' | '<=' | '>=' | '>' | '<'
    ;
pred
    : '\\true'                          # logical_true_pred
    | '\\false'                         # logical_false_pred
    | term (rel_op term)+               # comparison_pred
    | ident '(' term (',' term)* ')'    # predicate_application_pred
    | '(' pred ')'                      # parentheses_pred
    | pred '&&' pred                    # conjunction_pred
    | pred '||' pred                    # disjunction_pred
    | pred '==>' pred                   # implication_pred
    | pred '<==>' pred                  # equivalence_pred
    | '!' pred                          # negation_pred
    | pred '^^' pred                    # exclusive_or_pred
    | term '?' pred ':' pred            # ternary_condition_term_pred
    | pred '?' pred ':' pred            # ternary_condition_pred
    | '\\let' id '=' term ';' pred      # local_binding_pred
    | '\\let' id '=' pred ';' pred      # local_binding_pred
    | '\\forall' binders ';' pred       # universal_quantification_pred
    | '\\exists' binders ';' pred       # existential_quantification_pred
    | id ':' pred                       # syntactic_naming_pred
    | string ':' pred                   # syntactic_naming_pred
// oldandresult.tex
    | '\\old' '(' pred ')'              # old_pred
// loc.tex
    | '\\subset' '(' tset ',' tset ')'  # set_inclusion_pred
    | term '\\in' tset                  # set_membership_pred
// memory.tex:
    | '\\allocable' one_label? '(' term ')'                         # allocable_pred
    | '\\freeable' one_label? '(' term ')'                          # freeable_pred
    | '\\fresh'   two_labels? '(' term ',' term ')'                 # fresh_pred
    | '\\valid'  one_label?  '(' location_address ')'               # valid_pred
    | '\\valid_read'  one_label? '(' location_address ')'           # valid_read_pred
    | '\\separated' '(' location_address ',' location_addresses ')' # separated_pred
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
    : '*/' {skipCommentSymbols = false;}
    ;

AcslCommentIntermediate
    : '@' { if (skipCommentSymbols) skip(); }
    ;

acsl_comment
    : AcslCommentStart Newline* function_contract AcslCommentEnd Newline*
    ;
// own additions --- end