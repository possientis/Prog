shopt -s expand_aliases
alias coq='coqtop -Q Core Core -Q Lang1 Lang1 -Q Utils Utils -Q Lam Lam -Q Fol Fol "$@"'
