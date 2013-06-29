if exists("b:did_ftplugin")
  finish
endif


" Behaves just like Verilog
runtime! ftplugin/verilog.vim

" Extend matchit plugin
let b:match_words .=
  \ ',\<fork\>:\<join|join_any|join_none\>,' .
  \ ',\<class\>:\<endclass\>' .
  \ ',\<package\>:\<endpackage\>' .
  \ ',\<sequence\>:\<endsequence\>' .
  \ ',\<clocking\>:\<endclocking\>' .
  \ ',\<interface\>:\<endinterface\>' .
  \ ',\<covergroup\>:\<endgroup\>' .
  \ ',\<program\>:\<endprogram\>' .
  \ ',\<property\>:\<endproperty\>'
