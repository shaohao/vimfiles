#!/bin/bash

git subtree pull --prefix=bundle/LeaderF      https://github.com/Yggdroot/LeaderF.git      master  --squash
git subtree pull --prefix=bundle/indentLine   https://github.com/Yggdroot/indentLine.git   master  --squash

git subtree pull --prefix=bundle/rainbow      https://github.com/luochen1990/rainbow.git   master  --squash
git subtree pull --prefix=bundle/fencview     https://github.com/mbbill/fencview.git       master  --squash
git subtree pull --prefix=bundle/coc.nvim     https://github.com/neoclide/coc.nvim.git     release --squash
git subtree pull --prefix=bundle/vim-monokai  https://github.com/sickill/vim-monokai.git   master  --squash
git subtree pull --prefix=bundle/vim-surround https://github.com/tpope/vim-surround.git    master  --squash

git subtree pull --prefix=bundle/verilog_systemverilog.vim https://github.com/vhda/verilog_systemverilog.vim master --squash

git subtree pull --prefix=bundle/Align        https://github.com/vim-scripts/Align.git     master  --squash
git subtree pull --prefix=bundle/VisIncr      https://github.com/vim-scripts/VisIncr.git   master  --squash
git subtree pull --prefix=bundle/LargeFile    https://github.com/vim-scripts/LargeFile.git master  --squash
