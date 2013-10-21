if exists("b:did_ftplugin")
  finish
endif


" Behaves just like Verilog
runtime! ftplugin/verilog.vim

" Extend matchit plugin
let b:match_words .=
  \ ',\<fork\>:\<join|join_any|join_none\>' .
  \ ',\<class\>:\<endclass\>' .
  \ ',\<package\>:\<endpackage\>' .
  \ ',\<sequence\>:\<endsequence\>' .
  \ ',\<clocking\>:\<endclocking\>' .
  \ ',\<interface\>:\<endinterface\>' .
  \ ',\<covergroup\>:\<endgroup\>' .
  \ ',\<program\>:\<endprogram\>' .
  \ ',\<property\>:\<endproperty\>'

" Extend tagbar plugin
let g:tagbar_type_systemverilog = {
  \ 'ctagstype': 'systemverilog',
  \ 'kinds': [
    \ 'e:clocking',
    \ 'i:constraint',
    \ 'l:covergroup',
    \ 'o:class',
    \ 't:function',
    \ 'A:interface',
    \ 'G:module',
    \ 'J:package',
    \ 'M:program',
    \ 'W:task'
  \ ]
\ }
