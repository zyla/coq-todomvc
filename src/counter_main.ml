open Tea.App
open Counter

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
