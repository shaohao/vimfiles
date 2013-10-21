"-=[ Plugin Manager ]=-
runtime bundle/vim-pathogen/autoload/pathogen.vim
call pathogen#infect()

"-=[ Normal Settings ]=-
" Enable backspace
set backspace=2
"Highlight the screen line of the cursor
set cursorline
"Highlight the screen column of the cursor
"set cursorcolumn
"Highlight the maximum text width marker for version >= 7.3
if version >= 703
	set colorcolumn=80
endif
"Disable compatible
set nocompatible
"Always show tab line
set showtabline=2
"Enable the use of mouse
"set mouse=nvchr
set mouse=a
"Switch wrapping off
set nowrap
"Highlighting search
set hlsearch
"Enable status line
set laststatus=2
"Customize the list mode
if &encoding == "utf-8"
	set list listchars=eol:¬,tab:│┈,trail:·,extends:»,precedes:«,nbsp:&
else
	set list listchars=eol:<,tab:>-,trail:-,extends:>,precedes:<,nbsp:&
endif
if version >= 703
	if &encoding == "utf-8"
		set listchars+=conceal:┅
	else
		set listchars+=conceal:.
	endif
endif
"Status line text
set statusline=%=%y\ \|\ r%l,c%c%V\ \|\ 0x%02B\ \|\ %{&fileencoding}\ \|\ %r\ \|\ %{&fileformat}
"File encodings
set fileencodings=ucs-bom,utf-8,cp936,gb18030,big5,euc-jp,euc-kr,latin1
" Set backup directory
set backupdir=~/.vim/backup,/tmp
"Re-position cursor when re-opening files
autocmd BufReadPost * if line("'\"") > 0 && line("'\"") <= line("$") | exe "normal g`\"" | endif
"General File formats
syntax on
filetype plugin indent on
set ci si

"-=[ Programming Languages ]=-
"C/C++
autocmd FileType c,cpp,cs set cindent tabstop=4 shiftwidth=4 noexpandtab

"Verilog/SystemVerilog
autocmd FileType verilog,systemverilog set tabstop=8 shiftwidth=2 shiftround softtabstop=2 expandtab
autocmd FileType verilog,systemverilog set efm=%.%#**\ %t%.%#:%.%#\ %f(%l)\:\ %m

"Python
autocmd BufReadPre,BufNewFile *.py let python_highlight_all=1
autocmd FileType python set tabstop=8 softtabstop=4 shiftwidth=4 shiftround expandtab
autocmd FileType python set makeprg=python2\ %
"autocmd FileType python set efm=%C\ %.%#,%A\ \ File\ \"%f\"\\,\ line\ %l%.%#,%Z%[%^\ ]%\\@=%m
autocmd FileType python set efm=%-GTraceback%.%#\:,%A%>\ \ File\ \"%f\"\\,\ line\ %l%.%#,%C\ \ \ \ %.%#,%Z%[%^\ ]%\\@=%m

"Tcl/Tk
autocmd BufRead,BufNewFile *.do,*.tm,.tclshrc,.wishrc set filetype=tcl
autocmd FileType tcl set tabstop=8 shiftwidth=4 softtabstop=4 expandtab
autocmd FileType tcl set makeprg=wish\ %
autocmd FileType tcl set efm=%AError%.%#:\ %m,%C\ \ \ \ while%.%#,%Z\ \ \ \ \(file\ \"%f\"\ line\ %l%.%#

"Perl
autocmd FileType perl set cindent tabstop=8 shiftwidth=4 softtabstop=4 shiftround expandtab
autocmd FileType perl set makeprg=perl\ %
autocmd FileType perl set efm=%mat\ %f\ line\ %l%.%#

"Lua
autocmd FileType lua set tabstop=8 softtabstop=4 shiftwidth=4 shiftround expandtab

"Java
autocmd FileType java set tabstop=8 softtabstop=4 shiftwidth=4 shiftround expandtab

"NFO file
function! SetFileEncodings(encodings)
	let b:myfileencodingsbak = &fileencodings
	let &fileencodings=a:encodings
endfunction
function! RestoreFileEncodings()
	let &fileencodings = b:myfileencodingsbak
	unlet b:myfileencodingsbak
endfunction
autocmd BufReadPre *.nfo call SetFileEncodings('cp437') | set ambiwidth=single
autocmd BufReadPost *.nfo call RestoreFileEncodings()

"Django template
autocmd BufReadPost,BufNewFile *.html set ft=htmldjango softtabstop=4 tabstop=4 shiftwidth=4 shiftround noexpandtab

"Javascript (jQuery)
autocmd FileType javascript set cindent tabstop=4 shiftwidth=4 syntax=jquery noexpandtab

"-=[ Binding Kyes ]=-
"Create a new tab
nmap <C-N> <Esc>:tabnew<CR>
"Next/Previous marker in QuickFix Window
nmap <F3> :cp<CR>
nmap <F4> :cn<CR>
"Make Debugger
nmap <F5> :mak<CR>
"View page like a web browser
nmap <SPACE> <C-D>

"-=[ Plugins ]=-
"netrw
let g:netrw_altv = 1
let g:netrw_browse_split = 4
let g:netrw_liststyle = 3
let g:netrw_preview = 1
let g:netrw_winsize = 80

"neocompcache
let g:neocomplcache_enable_at_startup = 1
inoremap <expr><CR>  neocomplcache#smart_close_popup() . "\<CR>"
inoremap <expr><TAB>  pumvisible() ? "\<C-n>" : "\<TAB>"
inoremap <expr><C-h> neocomplcache#smart_close_popup()."\<C-h>"
inoremap <expr><BS> neocomplcache#smart_close_popup()."\<C-h>"
inoremap <expr><C-y>  neocomplcache#close_popup()
inoremap <expr><C-e>  neocomplcache#cancel_popup()

"Tagbar
nnoremap <silent> <F9> :TagbarToggle<CR>
"Cscope
if has("cscope")
	set csprg=/usr/bin/cscope
	set csto=0
	set cst
	set nocsverb
	" add any database in current directory
	if filereadable(".cscope/cscope.out")
		cs add .cscope/cscope.out
	" else add database pointed to by environment
	elseif $CSCOPE_DB != ""
		cs add $CSCOPE_DB
	endif
	set csverb
endif

"-=[ Customized functions ]=-
" Insert line number at the head of each line
function ILN(delim)
	let l:bln = line(".")
	" get the width of the maximum line number
	let l:width = strlen(line("$")+1)
	let l:cln = l:bln
	while 1
		let l:rep = l:width - strlen(l:cln-l:bln+1)
		if l:rep > 0
			execute "normal " . l:rep . "gI "
			execute "normal a" . (l:cln-l:bln+1) . a:delim
		else
			execute "normal i" . (l:cln-l:bln+1) . a:delim
		endif
		normal j
		normal 0
		let l:nln = line(".")
		if l:cln == l:nln
			break
		else
			let l:cln = l:nln
		endif
	endwhile
endfunction
" Format the code with prepending and appending sapce
function CFT()
	normal i 
	normal w
	normal a 
endfunction
map <F7> :call CFT()<CR>
