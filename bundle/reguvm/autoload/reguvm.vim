" Protection {{{1
if exists("g:loaded_reguvm")
  finish
endif
let g:loaded_reguvm = 1

" variables {{{1
let g:URMRegs = {}
let g:URMBlocks = {}

let s:topblk = ""
let s:topinst = ""

" -----------------------------------------------------------------------------
" s:LoadRegModel: Load register model from systemverilog file {{{1
function! s:LoadRegModel(svfn)
  let g:URMRegs = {}
  let g:URMBlocks = {}

  if !filereadable(a:svfn)
    return
  endif

  let reg = ''
  let block = ''
  let cls = ''
  for line in readfile(a:svfn)
    if line =~ '^\s*\/\/' || line =~ '^\s*$'
      continue
    endif
    let m = matchlist(line, '\s*class\s\+\(\w\+\)\s\+extends\s\+uvm_reg;')
    if len(m) > 1
      let reg = m[1]
      if !has_key(g:URMRegs, reg)
        let g:URMRegs[reg] = {
              \ 'name': reg,
              \ 'type': 'register',
              \ 'fields': [],
              \}
      endif
      let cls = 'reg'
    else
      let m = matchlist(line, '\s*class\s\+\(\w\+\)\s\+extends\s\+uvm_reg_block;')
      if len(m) > 1
        let block = m[1]
        let cls = 'blk'
        if !has_key(g:URMBlocks, block)
          let g:URMBlocks[block] = { 'name': block, 'type': 'block', 'comps': {} }
        endif
      endif
    endif

    if cls ==# 'reg'
      let m = matchlist(line, '\s*\(\w\+\)\.configure(\(.\+\));')
      if len(m) > 2
        let fname = m[1]
        let props = split(m[2], ',\s*', 1)
        call add(g:URMRegs[reg].fields, {
              \ 'name': fname,
              \ 'access': substitute(props[3], '"', '', 'g'),
              \ 'offset': props[2],
              \ 'width': props[1],
              \})
      endif
    elseif cls ==# 'blk'
      let m = matchlist(line, '\s*\([a-zA-Z_][0-9a-zA-Z_\[\]]*\)\s*=\s*\([a-zA-Z_][0-9a-zA-Z_\[\]]*\)::type_id::create\>')
      if len(m) > 2 && m[1] !~ '_cg$'
        let g:URMBlocks[block].comps[m[1]] = {
              \ 'name': m[2],
              \ 'inst': m[1],
              \ 'access': '',
              \ 'address': '',
              \}
      else
        let m = matchlist(line, '\s*\w\+\.add_reg(\([a-zA-Z_][0-9a-zA-Z_\[\]]*\),\s*\(.\+\),\s*"\(\w\+\)");')
        if len(m) > 3
          if has_key(g:URMBlocks[block].comps, m[1])
            let g:URMBlocks[block].comps[m[1]].address = m[2]
            let g:URMBlocks[block].comps[m[1]].access = substitute(m[3], '"', '', 'g')
          endif
        endif
      endif
    endif
  endfor
endfunction

" s:FieldCompare: Compare field with offset {{{1
function s:FieldCompare(i1, i2)
  return a:i1.offset - a:i2.offset
endfunction

" reguvm#GetCandidates: Get the final components from block tree {{{1
function reguvm#GetCandidates(path)
  if !len(a:path)
    let comp = { 'name': s:topblk, 'inst': s:topinst }
    return { 'name': s:topinst, 'type': 'block', 'comps': { s:topinst : comp } }
  endif

  let pblk = reguvm#GetCandidates(a:path[:-2])
  if has_key(pblk, 'comps') && has_key(pblk.comps, a:path[-1])
    let comp = pblk.comps[a:path[-1]]
    if has_key(g:URMBlocks, comp.name)
      return g:URMBlocks[comp.name]
    elseif has_key(g:URMRegs, comp.name)
      return g:URMRegs[comp.name]
    endif
  endif
  return { 'type': '#NA#' }
endfunction

" -----------------------------------------------------------------------------

" reguvm#install: Installation {{{1
function! reguvm#install(topblk, topinst, regsv)
  let s:topblk = a:topblk
  let s:topinst = a:topinst
  if !exists('g:neocomplcache_force_omni_patterns')
    let g:neocomplcache_force_omni_patterns = {}
  endif
  if !exists('g:neocomplcache_omni_functions')
    let g:neocomplcache_omni_functions = {}
  endif
  let g:neocomplcache_force_omni_patterns.systemverilog =
    \ '\<' . a:topinst . '\%(\(\.\w*\)\+\)'
  let g:neocomplcache_omni_functions.systemverilog = 'reguvm#CompleteURM'
  call s:LoadRegModel(a:regsv)
endfunction

" reguvm#CompleteURM: omnifunc {{{1
function! reguvm#CompleteURM(findstart, base)
  if a:findstart
    " locate the start of the word
    let line = getline('.')
    let start = col('.') - 1
    " back to `s:topinst.'
    while start > 0 && line[start - 1] =~ '\a'
      let start -= 1
    endwhile
    return start
  else
    " find block/register matching with "a:base"
    let matches = []
    let res = { 'words': matches }
    let line = getline('.')
    let col = col('.') - 1
    let start = col
    while start > 0 && line[start-7:start] !~ s:topinst . '\.'
      let start -= 1
    endwhile
    let start -= 7
    let path = split(line[start+0:col+0], '\.', 1)
    let candidate = reguvm#GetCandidates(path[:-2])
    if candidate.type ==# 'block'
      let comps = candidate.comps
      for m in sort(keys(comps))
        if m =~ '^' . a:base
          call add(matches, {
                \ 'word': m,
                \ 'menu': comps[m].access,
                \})
        endif
      endfor
    elseif candidate.type ==# 'register'
      let fields = candidate.fields
      for f in sort(fields, 's:FieldCompare')
        if f.name =~ '^' . a:base
          call add(matches, {
                \ 'word': f.name,
                \ 'abbr': '[' . f.offset . ':' . (f.offset+f.width-1) . ']' . f.name,
                \ 'menu': f.access,
                \})
        endif
      endfor
      let matches += ['read', 'write']
    endif
    if v:version < 704
      return matches
    else
      return res
    endif
  endif
endfunction

" vim: tw=8 sts=2 sw=2 et fdm=marker
