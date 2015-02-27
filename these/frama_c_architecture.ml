open Mlpost
open Box

(* Some custom values *)

let padding = Num.bp 15.
let big_padding = Num.bp 30.
let delta = Num.bp 5.
let big_delta = Num.bp 10.

let big_title s = tex ("\\textbf{\\Large{" ^ s ^ "}}")
let small_title s = tex ("\\textbf{\\emph{\\large{" ^ s ^ "}}}")

let external_color = Color.rgb8 255 165 0
let framac_color = Color.rgb8 50 205 50
let cil_color = Color.lightcyan
let plugin_color = Color.rgb8 250 128 114
let libraries_color = Color.orange

let std_box ?stroke ?color s = rect ~name:s ?stroke ?fill:color (tex s)
let mk_services ?(big=false) ?color title b = 
  round_rect 
    ?fill:color
    ~name:title 
    ~dx:padding ~dy:(if big then big_delta else delta)
    (vbox ~padding:(if big then Num.multn big_delta (Num.pt 1.5) else big_delta)
       [ (if big then big_title else small_title) title; b ])

(* Backend *)

let kernel_backend =
  mk_services ~big:true ~color:cil_color
    "Kernel Back-end"
    (hbox ~padding
       [ std_box "untyped2ast";
         std_box "c2untyped";
         std_box "runtime" ])

(* Frontend *)

let kernel_ast =
  mk_services "ASTs" (vbox ~padding [ std_box "ast"; std_box "untyped\\_ast" ])

let kernel_ai =
  mk_services "AI"
    (vbox ~padding [ std_box "memory\\_states"; std_box "abstract\\_interp" ])

let kernel_services =
  mk_services "General Services"
    (vbox ~padding
       [ std_box "cmdline\\_parameters";
         std_box "plugin\\_entry\\_points" ])

let kernel_trip =
  mk_services "AST Trip"
    (hbox ~padding [ std_box "visitor"; std_box "analysis" ])

let kernel_frontend =
      mk_services ~big:true "Kernel Front-end" ~color:framac_color
        (hbox ~padding
           [ vbox ~padding [ kernel_trip; kernel_ai ];
             vbox ~padding [ kernel_ast; kernel_services ] ])

(* Plugins *)

let plugins =
  mk_services ~big:true "Plug-ins" ~color:plugin_color
    (hbox ~padding:big_padding
       [ std_box "plug-in 1";
         std_box "plug-in 2";
         std_box ~stroke:None "\\dots";
         std_box "plug-in $n$" ])

(* Libraries *)

let libraries =
  mk_services ~big:true "Libraries" ~color:libraries_color
    (vbox ~padding:big_padding
       [ std_box "stdlib";
         hbox ~padding [ std_box "datatype"; std_box "project" ];
         std_box "utils" ])

(* Global figure *)

let figure =
  vbox ~padding:big_padding
    [ plugins;
      hbox ~padding:big_padding [ kernel_frontend; libraries ];
      kernel_backend ]

let arrow ?(big=false) ?ind ?style src dst =
  let getf s = get s figure in
  let src = getf src in
  let dst = getf dst in
  if big then
    Helpers.box_arrow ?ind ?style ~color:Color.red ~pen:Pen.circle src dst
  else
    Helpers.box_arrow ?ind ?style src dst

let cmds =
  let style = Path.jTension 2.5 2.5 in
  let up = Path.vec Point.up in
  let down = Path.vec Point.down in
  let left = Path.vec Point.left in
  Command.seq
    [
      draw figure;
      arrow "memory\\_states" "abstract\\_interp";
      arrow "analysis" "visitor";
      arrow ~ind:left ~style:(Path.jTension 0.8 0.8) "utils" "stdlib";
      arrow "project" "stdlib";
      arrow "datatype" "stdlib";
      arrow "project" "datatype";
      arrow "datatype" "utils";
      arrow "project" "utils";
      arrow "utils" "datatype";
      arrow "stdlib" "datatype";
      arrow ~ind:down ~style "plug-in 1" "plug-in 2";
      arrow ~ind:down ~style "plug-in 2" "\\dots";
      arrow ~ind:down ~style "\\dots" "plug-in $n$";
      arrow ~ind:up ~style "plug-in 2" "plug-in 1";
      arrow ~ind:up ~style "plug-in $n$" "\\dots";
      arrow ~ind:up ~style "\\dots" "plug-in 2";
      arrow ~big:true "AI" "ASTs";
      arrow ~big:true "AI" "General Services";
      arrow ~big:true "General Services" "ASTs";
      arrow ~big:true "ASTs" "General Services";
      arrow ~big:true "AST Trip" "General Services";
      arrow ~big:true "AST Trip" "ASTs";
      (* inter-services arrow *)
      arrow ~big:true "Plug-ins" "Kernel Front-end";
      arrow ~big:true "Kernel Back-end" "Kernel Front-end" ;
      arrow ~big:true "Kernel Front-end" "Kernel Back-end" ;
      arrow ~ind:(Path.vec Point.up) ~big:true "Kernel Back-end" "Libraries";
      arrow ~big:true "Kernel Front-end" "Libraries";
      arrow ~ind:(Path.vec Point.down) ~big:true "Plug-ins" "Libraries";
    ]

let _ = Metapost.emit "frama_c_architecture" cmds
