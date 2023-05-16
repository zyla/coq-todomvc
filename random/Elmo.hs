type Model = Int

init :: Model
init = 0

type Msg = Increment | Decrement

update :: Model -> Msg -> Model
update model = \case
  Increment -> model + 1
  Decrement -> model - 1

view : Model -> Html Msg
view model =
  div []
    [ button [ onClick Decrement ] [ text "-" ]
    , div [] [ text (show model) ]
    , button [ onClick Increment ] [ text "+" ]
    ]