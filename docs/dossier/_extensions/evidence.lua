-- evidence.lua — Quarto Lua filter for evidence panels
-- Converts ::: {.evidence} divs to collapsible <details> blocks in HTML

function Div(el)
  if el.classes:includes("evidence") then
    if quarto.doc.is_format("html") then
      local open_tag = pandoc.RawBlock("html",
        '<details class="evidence-panel">\n<summary>Evidence</summary>')
      local close_tag = pandoc.RawBlock("html", '</details>')
      local blocks = pandoc.List({open_tag})
      blocks:extend(el.content)
      blocks:insert(close_tag)
      return blocks
    end
  end
end
