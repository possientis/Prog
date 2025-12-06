set encoding=utf-8
set nocompatible          " use vim settings rather than vi
colorscheme solarized

let $BASH_ENV="~/.bash_aliases"

syntax on                 " colouring based on syntax
filetype on
filetype plugin indent on " auto indentation based on syntax

set background=dark
set wildmenu              " makes tab options visible
set history=1000          " default is 20
set shell=/bin/bash
set number
set splitbelow
set splitright
set cursorline
set hlsearch
set incsearch
set showcmd
set tabstop=2
set shiftwidth=2
set expandtab
set laststatus=2
set t_Co=256
set nocp                  " no vi compatibility mode

" will conflict with verilog, beware !!
au BufRead,BufNewFile *.v set filetype=coq  
au! Syntax coq source /usr/share/vim/vim91/syntax/coq.vim

au BufRead,BufNewFile *.agda set filetype=agda
au! Syntax agda source /usr/share/vim/vim91/syntax/agda.vim

au BufRead,BufNewFile *.idr set filetype=idris
au! Syntax idris source /usr/share/vim/vim91/syntax/idris.vim

au BufRead,BufNewFile *.lean set filetype=lean
au! Syntax lean source /usr/share/vim/vim91/syntax/lean.vim

autocmd BufWritePre *.v %s/\s\+$//e

augroup coq_folding
  autocmd!
  autocmd FileType coq setlocal foldmethod=expr
  autocmd FileType coq setlocal foldexpr=CoqFold(v:lnum)
  autocmd FileType coq setlocal foldtext=CoqFoldText()
  autocmd FileType coq setlocal fillchars+=fold:\ 
  autocmd FileType coq highlight Folded term=NONE cterm=NONE gui=NONE
  autocmd FileType coq highlight link Folded Normal
  autocmd FileType coq setlocal foldminlines=0
augroup END

function! CoqFold(lnum)
  let line = getline(a:lnum)
  let prev = a:lnum > 1 ? getline(a:lnum - 1) : ''

  " Keep 'Proof.' visible
  if line =~ '^\s*Proof'
    return 0
  " Keep 'Qed.' visible
  elseif line =~ '^\s*Qed\.'
    return 0
  " First line AFTER 'Proof.' starts a fold (level 1)
  elseif prev =~ '^\s*Proof'
    return 1
  " Other lines inherit previous fold level
  else
    return '='
  endif
endfunction

function! CoqFoldText()
  return '+'
endfunction
