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
syn keyword splStatement	include procedure returns if else while return new var
syn keyword splStatement	assert assume requires ensures invariant null
syn keyword splTodo         contained TODO ToDo Todo todo XXX FIXME
" spl Types
syn keyword splType     Bool Int Node
syn region splType      start="Loc<" end=">" contains=splType
syn region splType      start="Set<" end=">" contains=splType
" Operators and special characters
syn match splOperator	"!"
syn match splOperator	"="
syn match splOperator	"&&"
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
syn region splString start=+"+ end=+"+ oneline
" spl Comments
syn region splComment start="/\*" end="\*/" contains=splTodo,@Spell
syn match  splComment "//.*" contains=splTodo,@Spell

" Class Linking
hi def link splStatement    Statement
hi def link splType	        Type
hi def link splComment      Comment
hi def link splOperator	    Special
hi def link splSpecial      Special
hi def link splString       String
hi def link splTodo	        Todo

let b:current_syntax = "spl"
