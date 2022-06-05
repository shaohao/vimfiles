#!/bin/bash

ACTION=$1

#PLG_DIR=pack/my/start
PLG_DIR=bundle

update_plugin() {
	local name=$1
	local repo=$2
	local branch=$3
	if [[ x"$ACTION" == x"add" ]]; then
		git subtree add  --prefix=$PLG_DIR/$name $repo $branch --squash
	else
		git subtree pull --prefix=$PLG_DIR/$name $repo $branch --squash
	fi
}

update_plugin LeaderF      https://github.com/Yggdroot/LeaderF.git      master
update_plugin indentLine   https://github.com/Yggdroot/indentLine.git   master

update_plugin rainbow      https://github.com/luochen1990/rainbow.git   master
update_plugin fencview     https://github.com/mbbill/fencview.git       master
update_plugin coc.nvim     https://github.com/neoclide/coc.nvim.git     release
update_plugin vim-monokai  https://github.com/sickill/vim-monokai.git   master
update_plugin vim-surround https://github.com/tpope/vim-surround.git    master

update_plugin verilog_systemverilog.vim https://github.com/vhda/verilog_systemverilog.vim master

update_plugin Align        https://github.com/vim-scripts/Align.git     master
update_plugin VisIncr      https://github.com/vim-scripts/VisIncr.git   master
update_plugin LargeFile    https://github.com/vim-scripts/LargeFile.git master
