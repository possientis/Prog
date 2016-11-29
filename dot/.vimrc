set nocompatible          " use vim settings rather than vi
set background=dark
syntax on                 " colouring based on syntax
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

set tabstop=2
set shiftwidth=2
set expandtab
set laststatus=2
colorscheme solarized

set encoding=utf-8
set t_Co=256

" will conflict with verilog, beware !!
au BufRead,BufNewFile *.v set filetype=coq  
au! Syntax coq source /usr/share/vim/vim80/syntax/coq.vim
