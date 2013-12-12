#!/bin/bash

git subtree pull --prefix=bundle/neocomplcache https://github.com/Shougo/neocomplcache.vim.git master --squash
git subtree pull --prefix=bundle/syntastic     https://github.com/scrooloose/syntastic.git     master --squash
git subtree pull --prefix=bundle/tagbar        https://github.com/majutsushi/tagbar.git        master --squash
git subtree pull --prefix=bundle/vim-surround  https://github.com/tpope/vim-surround.git       master --squash
git subtree pull --prefix=bundle/vim-pathogen  https://github.com/tpope/vim-pathogen.git       master --squash
git subtree pull --prefix=bundle/ack.vim       https://github.com/mileszs/ack.vim.git          master --squash
git subtree pull --prefix=bundle/vcscommand    git://repo.or.cz/vcscommand.git                 master --squash
