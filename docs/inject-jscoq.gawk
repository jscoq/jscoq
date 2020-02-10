BEGINFILE { has=0 }
/\/jscoq\// { has=1 }
/<[/]html>/ && has<1 {
    print "  <script src=\"node_modules/jscoq/ui-js/jscoq-loader.js\"></script>" 
    print "  <script src=\"jscoq-embed.js\"></script>"
}
{ print }