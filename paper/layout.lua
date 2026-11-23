local function tex(code)
  return pandoc.RawBlock('latex', code)
end

local function cover_field(block)
  -- Let the LaTeX writer escape names and format links from the Markdown cover.
  local field = pandoc.Plain(block.content):walk({
    LineBreak = function() return pandoc.RawInline('latex', '\\\\[10pt]') end
  })
  return pandoc.write(pandoc.Pandoc({field}), 'latex')
end

function Pandoc(doc)
  local blocks = doc.blocks
  assert(#blocks >= 8 and blocks[1].t == 'Header'
    and blocks[8].t == 'Header' and pandoc.utils.stringify(blocks[8]) == 'Abstract',
    'Expected a cover with title, subtitle, author, ORCID, LinkedIn, version and date before the abstract')

  local fields = {}
  for i = 1, 7 do
    fields[i] = '{' .. cover_field(blocks[i]) .. '}'
  end
  local result = {tex('\\PaperCover' .. table.concat(fields)), tex([[\vbox to \textheight{\vfil\hbox{\begin{minipage}{\textwidth}\PaperParagraphs]])}
  local in_abstract = true
  for i = 8, #blocks do
    local block = blocks[i]
    if i > 8 and block.t == 'Header' and block.level == 1 then
      if in_abstract then
        table.insert(result, tex([[\end{minipage}}\vfil}\clearpage\tableofcontents\clearpage]]))
        in_abstract = false
      end
    elseif block.t == 'Para' and block.content[1].t == 'Strong'
      and pandoc.utils.stringify(block.content[1]):match('^Theorem 9%.1 ') then
      table.insert(result, tex([[\needspace{8\baselineskip}]]))
    end
    if block.t == 'Table' then
      table.insert(result, tex([[\par\noindent\begin{minipage}{\linewidth}]]))
      table.insert(result, block)
      table.insert(result, tex([[\end{minipage}\par]]))
    else
      table.insert(result, block)
    end
  end
  return pandoc.Pandoc(result, doc.meta)
end
