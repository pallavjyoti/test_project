" Author: Pallav Jyoti Barman (pallavjyoti@gmail.com)
" Version: 1.0
" Last Modified: 09.02.2014
" License: http://www.opensource.org/licenses/bsd-license.php
" Basically, you are free to use the code as is or modified for whatever purpose,
" provided you include the above header and the same license. The code is provided
" "as is" without any express or implied warranties.
"
" Description:
" Expands various special expressions in V/SV source files.
" Nothing is expanded within strings and within comments if the
" line starts with // (line comment), /* or * (assumed to be a
" part of a comment). Should work fine with common formatting.
" Beware though that it will expand in
" /*
"  some code here
"  */
"
" Keyboard mappings are located at the very end of the file.
"
" The current functionality can be devided into two categories:
"   Loop and block expansion
"   Container and type expansion
"
" Future improvements will include the following:
"   Declarations with initialization
"       e.g. @vi V x y z
"               vector<int> V;
"               V.push_back(x);
"               V.push_back(y);
"               V.push_back(z);
"   Debugging output printing
"       e.g. @dbg x y z
"               //@
"               cerr << "x = " << x << " y = " << y << " z = " << '\n';
"               //@
"
"       also printing templates for vectors, arrays etc., also delimited with the special 
"       //@ comment
"
"       A dedicated function will then comment the debugging code in/out (toggle)
"
"
"   1. Loop and block expansion
"       
"       Loop and block expansion will only happen on start of lines and after "} else"
"       on the start of a line (module whitespace).
"       Will work fine if standard formatting is used.
"       The cursor is positioned inside the (empty) block with an additional
"       indent level (standard K&R style)
"
"       @f var_name upper_limit
"           for (int var_name=0; var_name<upper_limit; ++var_name) {
"               
"           }
"       @f var_name lower_limit upper_limit
"           for (int var_name=lower_limit; var_name<upper_limit; ++var_name) {
"               
"           }
"       @fd var_name upper_limit
"           for (int var_name=upper_limit-1; var_name>=0; --var_name) {
"               
"           }
"       @fd var_name lower_limit upper_limit
"           for (int var_name=upper_limit-1; var_name>=lower_limit; --var_name) {
"               
"           }
"
"       upper_limit can be a vector (or some other object) name preceeded by a #, 
"       in which case it gets expanded into (int)upper_limit.size()
"
"       @i expression
"           if (expression) {
"               
"           }
"       @w expression
"           while (expression) {
"               
"           }
"       @d expression
"           do {
"               
"           } while (expression);
"
"       @iter iter_name <container expansion expression> container_name
"           for (<expanded container expnasion expression>::iterator iter_name=container_name.begin(); iter_name!=container_name.end(); ++iter_name) {
"               
"           }
"       @iterc iter_name <container expansion expression> container_name
"           for (<expanded container expnasion expression>::const_iterator iter_name=container_name.begin(); iter_name!=container_name.end(); ++iter_name) {
"               
"           }
"
"
"   2. Container and type expansion
"
"       @ds
"       @di
"

if exists("uvm_expansion_loaded")
    finish
endif
let uvm_expansion_loaded = 1

function! Sv_uvmExpand()
    " This function should be called for individual lines.
    " Returns 1 if something was changed, 0 otherwise
    let line = getline('.')
    let original_line = line

    " don't replace inside comments (approximation; see top of file)
    " and exit early if there is no 'magic' token '@'
    if stridx(line, '@')==-1 || match(line, '^\s*\%(\/\/\|\/\*\|\*\)')!=-1
        return 0
    endif
    

    " indentation calculation (easier way?)
    let ind = '' " indentation string (all spaces)
    let t = indent('.')
    let ind_count = t
    let end_col = t
    while t > 0
        let t = t - 1
        let ind = ind . ' '
    endwhile
    let one_tab = ''
    let t = &tabstop
    let end_col = end_col + t
    while t > 0
        let t = t - 1
        let one_tab = one_tab . ' '
    endwhile

    let line_num = line('.') + 1 " final cursor line after expansion of loops and blocks
    " end of indentation calculation

    " special logic for lines that start with "} else" to allow expansions 
    " in idiomatic if/else if/.../else construcs
    let else_part = ''
    if match(line, '^\s*} else ') != -1
        let else_part = ind . '} else '
        let line = strpart(line, ind_count + 7) " len('} else ') == 7
    endif

    " @iter and @iterc
    let iter = match(line, '^\s*@iter ')
    let iterc = match(line, '^\s*@iterc ')
    if iter!=-1 || iterc!=-1
        let iter_type = ''
        if iter != -1
            let iter_type = '::iterator'
        else
            let iter_type = '::const_iterator'
        endif

        let components = split(line, ' ', 0) " 0 is not to keep empty entries
        if len(components) == 4 " if there's a different number of components, assume an error and do nothing
            let iter_name = components[1]
            let container_expression = components[2]
            let container_name = components[3]
            " only modify line but don't set it; container_expression must be expanded afterwards, and then the line will be set
            let line = 'for (' . container_expression . iter_type . ' ' . iter_name . '=' . container_name . '.begin(); ' . iter_name . '!=' . container_name . '.end(); ++' . iter_name . ') {'
            if else_part == ''
                let line = ind . line
            endif
            " append loop footer
            call append('.', [ind . one_tab, ind . '}'])
        endif
    endif

    " container and type expansion
    " to avoid replacing inside strings, split the line
    let components = split(line, '"', 1) " 1 is to keep empty entries

    " every second component is a non string, so replace within it
    let i = 0
    let sz = len(components)
    while i < sz
        let line = components[i]

        " display expansion
        let line = substitute(line, '@ds', '$display("");', 'g')
        let line = substitute(line, '@di', '$display("%d",);', 'g')
	" rand expansion
	" coverage expansion
	"

        let components[i] = line
        let i += 2
    endwhile
    
    " put it back together
    let line = join(components, '"')
    " end of container and type expansion
    let line_changed = 0
    if line != original_line
        let line_changed = 1
    endif

    " all the other expansions only happen at the start of lines (possibly preceded by
    " whitespace) and start with @ ('} else' handling is done separately and does not 
    " affect this stage except when setting the line)
    " this will also stop if iter or iterc were set since 'line' will not start with @
    if match(line, '^\s*@') == -1 
        call setline('.', else_part . line)
        if iter!=-1 || iterc!=-1
            call cursor(line_num, end_col)
        endif
        return line_changed
    endif

    " for loop expansion
    if match(line, '^\s*@f') != -1
        let components = split(line, '\s\+', 0)
        let sz = len(components) " expect 3 or 4
        if sz<3 || sz>4
            return line_changed
        endif

        " expand upper_limit
        let var_name = components[1]
        let upper_limit = components[sz-1]
        let upper_limit = substitute(upper_limit, '^#\(.*\)$', '(int)\1\.size()', '')

        if sz == 3
            if components[0] == '@f'
                call setline('.', ind . else_part . 'for (int ' . var_name . '=0; ' . var_name . '<' . upper_limit . '; ++' . var_name . ') {')
            elseif components[0] == '@fd'
                call setline('.', ind . else_part . 'for (int ' . var_name . '=' . upper_limit . '-1; ' . var_name . '>=0; --' . var_name . ') {')
            endif
        else
            let lower_limit = components[2]
            if components[0] == '@f'
                call setline('.', ind . else_part . 'for (int ' . var_name . '=' . lower_limit . '; ' . var_name . '<' . upper_limit . '; ++' . var_name . ') {')
            elseif components[0] == '@fd'
                call setline('.', ind . else_part . 'for (int ' . var_name . '=' . upper_limit . '-1; ' . var_name . '>=' . lower_limit . '; --' . var_name . ') {')
            endif
        endif
        call append('.', [ind . one_tab, ind . '}'])
        call cursor(line_num, end_col)
        return 1
    endif " for loop expansion

    " if/while/do expansion
    if match(line, '^\s*@[iwd] ') != -1
        let kw = ''
        if else_part != ''
            let kw = strpart(line, 1, 1)
        else
            let kw = strpart(line, ind_count + 1, 1)
        endif
                
        if kw == 'i'
            let kw = 'if'
        elseif kw == 'w'
            let kw = 'while'
        else
            let kw = 'do'
        endif

        let expression = ''
        if else_part != ''
            let expression = strpart(line, 3)
        else
            let expression = strpart(line, ind_count + 3)
        endif

        if kw=='if' || kw=="while"
            if else_part != ''
                call setline('.', else_part . kw . ' (' . expression . ') {')
            else
                call setline('.', ind . else_part . kw . ' (' . expression . ') {')
            endif
    
            call append('.', [ind . one_tab, ind . '}'])
        elseif kw == 'do'
            if else_part != ''
                call setline('.', else_part . 'do {')
            else
                call setline('.', ind . else_part . 'do {')
            endif

            call append('.', [ind . one_tab, ind . '} while (' . expression . ');'])
        endif
        call cursor(line_num, end_col)
        return 1
    endif " if/while/do expansion

    return line_changed
endfunction

function! Sv_uvmExpandWrapper()
    " Map this to <Enter> in insert mode.
    " Only does the expansion if the cursor is at the end of the line,
    " otherwise mimics normal <Enter> operation. Should work seamlessly.
    
    let line = getline('.')
    if len(line) == 0
        normal o
        return ''
    endif
    
    let cursor_pos = col('.')
    if cursor_pos == len(line) + 1
        if Sv_uvmExpand() == 1 
            call cursor('.', len(getline('.')) + 1)
            return ''
        endif
    endif

    " mimic normal <Enter> behavior
    let ind = ''
    
    " special case for lines that end with {
    " => add another tab to the indent level
    if match(line, '^.*{$') != -1
        let t = &tabstop
        while t > 0
            let ind = ind . ' '
            let t = t - 1
        endwhile
    endif
    call setline('.', strpart(line, 0, cursor_pos-1))
    let line = substitute(strpart(line, cursor_pos-1), '^\s+', '', '')
    let line_num = line('.') + 1
    let t = cindent('.')
    while t > 0
        let ind = ind . ' '
        let t = t - 1
    endwhile
    call append('.', ind . line)
    call cursor(line_num, indent(line_num) + 1)

    return ''
endfunction


