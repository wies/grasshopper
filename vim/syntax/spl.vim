" Vim syntax file
" Language:			SPL
" Maintainer:		Damien Zufferey <zufferey@csail.mit.edu>
" First Release:	???
" Last Change:		???
" Version:			0.1

if exists("b:current_syntax")
  finish
endif

" case is significant
" syn case ignore
" spl Keywords
syn keyword splStatement	include procedure returns if else while return new var null
syn keyword splStatement	axiom assert assume requires ensures invariant matching yields
syn keyword splStatement	struct function predicate pure ghost implicit
syn keyword splTodo         contained TODO ToDo Todo todo XXX FIXME
" spl Types
syn keyword splType     Bool Int Node
syn region splType      start="Array<" end=">" contains=splType
syn region splType      start="Loc<"   end=">" contains=splType
syn region splType      start="Set<"   end=">" contains=splType
" Operators and special characters
syn keyword splOperator exists forall
syn match splOperator	"!"
syn match splOperator	"="
syn match splOperator	"&&"
syn match splOperator	"&*&"
syn match splOperator	"||"
syn match splOperator	"!"
syn match splOperator	"+"
syn match splOperator	"*"
syn match splOperator	"/"
syn match splOperator	"-"
syn match splOperator	"<"
syn match splOperator	">"
syn match splSpecial	"\."
syn match splSpecial	"\["
syn match splSpecial	"\]"
syn match splSpecial 	":="
" literal
syn region splLiteral   start=+"+ end=+"+ oneline
syn keyword splLiteral  true false
syn match  splLiteral   "-\=\<\d\+\>"
syn match  splLiteral   "0x\x\+"
" spl Comments
syn region splComment start="/\*" end="\*/" contains=splTodo,@Spell
syn match  splComment "//.*" contains=splTodo,@Spell

" Class Linking
hi def link splStatement    Statement
hi def link splType	        Type
hi def link splComment      Comment
hi def link splOperator	    Special
hi def link splSpecial      Special
hi def link splLiteral      String
hi def link splTodo	        Todo

let b:current_syntax = "spl"
