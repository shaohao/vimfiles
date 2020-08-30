set nocompatible
filetype off


filetype plugin indent on

packadd! matchit

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
set ci si

"-=[ Programming Languages ]=-
set tabstop=4 shiftwidth=4 shiftround softtabstop=4 expandtab

"C/C++
autocmd FileType c,cpp,cs set cindent tabstop=4 shiftwidth=4 noexpandtab

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

"-=[ Binding Kyes ]=-
"Create a new tab
map <C-N> <Esc>:tabnew<CR>
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
let g:netrw_winsize = 70
"indentLine
let g:indentLine_char_list = ['|', '¦', '┆', '┊']
"rainbow
let g:rainbow_active = 1
let g:rainbow_conf = {
\	'guifgs': ['royalblue3', 'darkorange3', 'seagreen3', 'firebrick'],
\	'ctermfgs': ['lightblue', 'lightyellow', 'lightcyan', 'lightmagenta'],
\	'guis': [''],
\	'cterms': [''],
\	'operators': '_,_',
\	'parentheses': ['start=/(/ end=/)/ fold', 'start=/\[/ end=/\]/ fold', 'start=/{/ end=/}/ fold'],
\	'separately': {
\		'*': {},
\		'markdown': {
\			'parentheses_options': 'containedin=markdownCode contained',
\		},
\		'lisp': {
\			'guifgs': ['royalblue3', 'darkorange3', 'seagreen3', 'firebrick', 'darkorchid3'],
\		},
\		'haskell': {
\			'parentheses': ['start=/(/ end=/)/ fold', 'start=/\[/ end=/\]/ fold', 'start=/\v\{\ze[^-]/ end=/}/ fold'],
\		},
\		'vim': {
\			'parentheses_options': 'containedin=vimFuncBody',
\		},
\		'perl': {
\			'syn_name_prefix': 'perlBlockFoldRainbow',
\		},
\		'stylus': {
\			'parentheses': ['start=/{/ end=/}/ fold contains=@colorableGroup'],
\		},
\		'css': 0,
\	}
\}

"-=[ Customization ]=-
" Format the code with prepending and appending sapce
function CFT()
	normal i 
	normal w
	normal a 
endfunction
map <F7> :call CFT()<CR>

" Write with sudo
command W w !sudo tee % > /dev/null
