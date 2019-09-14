#!/bin/bash

git subtree pull --prefix=bundle/vim-go          https://github.com/fatih/vim-go.git               master --squash
git subtree pull --prefix=bundle/neocomplete.vim https://github.com/Shougo/neocomplete.vim.git     master --squash
git subtree pull --prefix=bundle/ctrlp.vim       https://github.com/kien/ctrlp.vim.git             master --squash
git subtree pull --prefix=bundle/syntastic       https://github.com/scrooloose/syntastic.git       master --squash
git subtree pull --prefix=bundle/tagbar          https://github.com/majutsushi/tagbar.git          master --squash
git subtree pull --prefix=bundle/vim-surround    https://github.com/tpope/vim-surround.git         master --squash
git subtree pull --prefix=bundle/vim-pathogen    https://github.com/tpope/vim-pathogen.git         master --squash
git subtree pull --prefix=bundle/ack.vim         https://github.com/mileszs/ack.vim.git            master --squash
git subtree pull --prefix=bundle/vcscommand.vim  https://github.com/vim-scripts/vcscommand.vim.git master --squash
git subtree pull --prefix=bundle/VisIncr         https://github.com/vim-scripts/VisIncr.git        master --squash
