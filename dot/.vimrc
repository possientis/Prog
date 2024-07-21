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
au! Syntax coq source /usr/share/vim/vim90/syntax/coq.vim

au BufRead,BufNewFile *.agda set filetype=agda
au! Syntax agda source /usr/share/vim/vim90/syntax/agda.vim

au BufRead,BufNewFile *.idr set filetype=idris
au! Syntax idris source /usr/share/vim/vim90/syntax/idris.vim

au BufRead,BufNewFile *.lean set filetype=lean
au! Syntax lean source /usr/share/vim/vim90/syntax/lean.vim

autocmd BufWritePre *.v %s/\s\+$//e
