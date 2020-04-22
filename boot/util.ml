module Result = struct
  let (let+) r f = Result.map f r
  let (and+) l r = match l, r with
    | Ok l, Ok r -> Ok(l, r)
    | Ok _, Error e -> Error e
    | Error e, _ -> Error e
  let (let*) = Result.bind
  let (and*) = (and+)
end

module Option = struct
  let (let+) opt f = Option.map f opt
  let (and+) l r = match l, r with
    | Some l, Some r -> Some(l, r)
    | _, _ -> None
  let (let*) = Option.bind
  let (and*) = (and+)
end
