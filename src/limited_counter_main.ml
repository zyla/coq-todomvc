open Tea.App
open LimitedCounter

let _ = 
  Js.Global.setTimeout
    (fun _ -> 

    beginnerProgram {
      model = App.init ();
      update = App.update;
      view = App.view;
    } (Web.Document.getElementById "app") () 
    |. ignore
    )  
  0
