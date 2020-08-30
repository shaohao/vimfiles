set nocompatible
filetype off

filetype plugin indent on

packadd! matchit

"{{{ Normal Settings
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
"}}}

"{{{ Programming Languages
set tabstop=4 shiftwidth=4 shiftround softtabstop=4 expandtab

"C/C++
autocmd FileType c,cpp,cs set cindent tabstop=4 shiftwidth=4 noexpandtab

"verilog/systemverilog
autocmd FileType verilog_systemverilog set autoindent

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
"}}}

"{{{ Binding Kyes
"Create a new tab
map <C-N> <Esc>:tabnew<CR>
"Next/Previous marker in QuickFix Window
nmap <F3> :cp<CR>
nmap <F4> :cn<CR>
"Make Debugger
nmap <F5> :mak<CR>
"Scroll page
nmap <SPACE> <C-D>
"}}}

"{{{ Plugins
"netrw
let g:netrw_altv = 1
let g:netrw_browse_split = 4
let g:netrw_liststyle = 3
let g:netrw_preview = 1
let g:netrw_winsize = 70
"indentLine
let g:indentLine_char_list = ['|', '¦', '┆', '┊']
"{{{ rainbow
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
"}}}
"{{{ LeaderF
let $GTAGSLABEL = 'native-pygments'
let $GTAGSCONF = '$HOME/.local/share/gtags/gtags.conf'
let g:Lf_WindowPosition = 'popup'
let g:Lf_PreviewinPopup = 1
let g:Lf_ShortcutF = '<C-P>'
let g:Lf_HideHelp = 1
let g:Lf_PreviewResult = {'Function':0, 'Colorscheme':1}
let g:Lf_NormalMap = {
    \ "File"   : [["<ESC>", ':exec g:Lf_py "fileExplManager.quit()"<CR>']],
    \ "Buffer" : [["<ESC>", ':exec g:Lf_py "bufExplManager.quit()"<CR>']],
    \ "Mru"    : [["<ESC>", ':exec g:Lf_py "mruExplManager.quit()"<CR>']],
    \ "Tag"    : [["<ESC>", ':exec g:Lf_py "tagExplManager.quit()"<CR>']],
    \ "Function": [["<ESC>", ':exec g:Lf_py "functionExplManager.quit()"<CR>']],
    \ "Colorscheme": [["<ESC>", ':exec g:Lf_py "colorschemeExplManager.quit()"<CR>']],
    \ }
noremap <F2> :LeaderfFunction!<cr>
"}}}
"{{{coc.nvim
" TextEdit might fail if hidden is not set.
set hidden

" Some servers have issues with backup files, see #649.
set nobackup
set nowritebackup

" Give more space for displaying messages.
set cmdheight=2

" Having longer updatetime (default is 4000 ms = 4 s) leads to noticeable
" delays and poor user experience.
set updatetime=300

" Don't pass messages to |ins-completion-menu|.
set shortmess+=c

" Always show the signcolumn, otherwise it would shift the text each time
" diagnostics appear/become resolved.
if has("patch-8.1.1564")
  " Recently vim can merge signcolumn and number column into one
  set signcolumn=number
else
  set signcolumn=yes
endif

" Use tab for trigger completion with characters ahead and navigate.
" NOTE: Use command ':verbose imap <tab>' to make sure tab is not mapped by
" other plugin before putting this into your config.
inoremap <silent><expr> <TAB>
      \ pumvisible() ? "\<C-n>" :
      \ <SID>check_back_space() ? "\<TAB>" :
      \ coc#refresh()
inoremap <expr><S-TAB> pumvisible() ? "\<C-p>" : "\<C-h>"

function! s:check_back_space() abort
  let col = col('.') - 1
  return !col || getline('.')[col - 1]  =~# '\s'
endfunction

" Use <c-space> to trigger completion.
if has('nvim')
  inoremap <silent><expr> <c-space> coc#refresh()
else
  inoremap <silent><expr> <c-@> coc#refresh()
endif

" Use <cr> to confirm completion, `<C-g>u` means break undo chain at current
" position. Coc only does snippet and additional edit on confirm.
" <cr> could be remapped by other vim plugin, try `:verbose imap <CR>`.
if exists('*complete_info')
  inoremap <expr> <cr> complete_info()["selected"] != "-1" ? "\<C-y>" : "\<C-g>u\<CR>"
else
  inoremap <expr> <cr> pumvisible() ? "\<C-y>" : "\<C-g>u\<CR>"
endif

" Use `[g` and `]g` to navigate diagnostics
" Use `:CocDiagnostics` to get all diagnostics of current buffer in location list.
nmap <silent> [g <Plug>(coc-diagnostic-prev)
nmap <silent> ]g <Plug>(coc-diagnostic-next)

" GoTo code navigation.
nmap <silent> gd <Plug>(coc-definition)
nmap <silent> gy <Plug>(coc-type-definition)
nmap <silent> gi <Plug>(coc-implementation)
nmap <silent> gr <Plug>(coc-references)

" Use K to show documentation in preview window.
nnoremap <silent> K :call <SID>show_documentation()<CR>

function! s:show_documentation()
  if (index(['vim','help'], &filetype) >= 0)
    execute 'h '.expand('<cword>')
  else
    call CocAction('doHover')
  endif
endfunction

" Highlight the symbol and its references when holding the cursor.
autocmd CursorHold * silent call CocActionAsync('highlight')

" Symbol renaming.
nmap <leader>rn <Plug>(coc-rename)

" Formatting selected code.
xmap <leader>f  <Plug>(coc-format-selected)
nmap <leader>f  <Plug>(coc-format-selected)

augroup mygroup
  autocmd!
  " Setup formatexpr specified filetype(s).
  autocmd FileType typescript,json setl formatexpr=CocAction('formatSelected')
  " Update signature help on jump placeholder.
  autocmd User CocJumpPlaceholder call CocActionAsync('showSignatureHelp')
augroup end

" Applying codeAction to the selected region.
" Example: `<leader>aap` for current paragraph
xmap <leader>a  <Plug>(coc-codeaction-selected)
nmap <leader>a  <Plug>(coc-codeaction-selected)

" Remap keys for applying codeAction to the current buffer.
nmap <leader>ac  <Plug>(coc-codeaction)
" Apply AutoFix to problem on the current line.
nmap <leader>qf  <Plug>(coc-fix-current)

" Map function and class text objects
" NOTE: Requires 'textDocument.documentSymbol' support from the language server.
xmap if <Plug>(coc-funcobj-i)
omap if <Plug>(coc-funcobj-i)
xmap af <Plug>(coc-funcobj-a)
omap af <Plug>(coc-funcobj-a)
xmap ic <Plug>(coc-classobj-i)
omap ic <Plug>(coc-classobj-i)
xmap ac <Plug>(coc-classobj-a)
omap ac <Plug>(coc-classobj-a)

" Use CTRL-S for selections ranges.
" Requires 'textDocument/selectionRange' support of LS, ex: coc-tsserver
nmap <silent> <C-s> <Plug>(coc-range-select)
xmap <silent> <C-s> <Plug>(coc-range-select)

" Add `:Format` command to format current buffer.
command! -nargs=0 Format :call CocAction('format')

" Add `:Fold` command to fold current buffer.
command! -nargs=? Fold :call     CocAction('fold', <f-args>)

" Add `:OR` command for organize imports of the current buffer.
command! -nargs=0 OR   :call     CocAction('runCommand', 'editor.action.organizeImport')

" Add (Neo)Vim's native statusline support.
" NOTE: Please see `:h coc-status` for integrations with external plugins that
" provide custom statusline: lightline.vim, vim-airline.
set statusline^=%{coc#status()}%{get(b:,'coc_current_function','')}

" Mappings for CoCList
" Show all diagnostics.
nnoremap <silent><nowait> <space>a  :<C-u>CocList diagnostics<cr>
" Manage extensions.
nnoremap <silent><nowait> <space>e  :<C-u>CocList extensions<cr>
" Show commands.
nnoremap <silent><nowait> <space>c  :<C-u>CocList commands<cr>
" Find symbol of current document.
nnoremap <silent><nowait> <space>o  :<C-u>CocList outline<cr>
" Search workspace symbols.
nnoremap <silent><nowait> <space>s  :<C-u>CocList -I symbols<cr>
" Do default action for next item.
nnoremap <silent><nowait> <space>j  :<C-u>CocNext<CR>
" Do default action for previous item.
nnoremap <silent><nowait> <space>k  :<C-u>CocPrev<CR>
" Resume latest coc list.
nnoremap <silent><nowait> <space>p  :<C-u>CocListResume<CR>
"}}}

"{{{ Customization
" Format the code with prepending and appending sapce
function CFT()
	normal i 
	normal w
	normal a 
endfunction
map <F7> :call CFT()<CR>

" Write with sudo
command W w !sudo tee % > /dev/null
"}}}

" vim: set fdm=marker:
