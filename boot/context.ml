type ('k,'v) t = {
    bindings : ('k, 'v) Hashtbl.t;
    parent : ('k, 'v) t option;
  }

let create () =
  { bindings = Hashtbl.create 7; parent = None }

let extend ctx =
  { bindings = Hashtbl.create 7; parent = Some ctx }

let rec find ctx key =
  match Hashtbl.find_opt ctx.bindings key with
  | Some v -> Some v
  | None -> Option.bind ctx.parent (fun ctx -> find ctx key)

let add ctx k v =
  match Hashtbl.find_opt ctx.bindings k with
  | Some _ -> false
  | None ->
     Hashtbl.add ctx.bindings k v;
     true
