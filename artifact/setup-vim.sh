#!/usr/bin/env bash
set -ex

sudo apt-get install -y vim vim-gtk

cat > ~/.vimrc <<EOF
set ai
set background=dark
set cc=80                   " cc = color column
set expandtab
set list                    " display whitespace
set listchars=trail:.       " display these differently
set nowrap                  " line wrapping
set nu                      " line numbers
set ruler                   " status at bottom right
set shiftwidth=4
set tabstop=2
syntax off

EOF

