# Design considerations for jsCoq

## Package Management:

Doing it in Ocaml vs doing it in Js.

### Js solution:

1. parse the json pkg file
2. download every every file, then `jsCoq.register_file(path, array)`
3. register Coq namespace `jsCoq.add_load_path(pkg_id, dir)`

### Current solution:

1. We load the packages in Ocaml, however it is very slow and we gain
   little as still a lot of marshalling overhead happens in order to communicate with the UI

## Dynamic vs Static linking of Coq plugins



## Printing
