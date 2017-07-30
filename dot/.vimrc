set encoding=utf-8
colorscheme solarized
syntax on                 " colouring based on syntax

set nocompatible          " use vim settings rather than vi
set background=dark
filetype plugin indent on " auto indentation based on syntax
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
set tabstop=4
set shiftwidth=4
set expandtab
set laststatus=2
set t_Co=256
set nocp                  " no vi compatibility mode

" will conflict with verilog, beware !!
au BufRead,BufNewFile *.v set filetype=coq  
au! Syntax coq source /usr/share/vim/vim80/syntax/coq.vim

au BufRead,BufNewFile *.agda set filetype=agda
au! Syntax agda source /usr/share/vim/vim80/syntax/agda.vim

