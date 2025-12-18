open Ppxlib

let ast ~loc =
  [%stri
    let initialState : [%t Uncurried.ty ~loc ~arity:1 [%type: input -> state]] =
      [%e
        Uncurried.fn
          ~loc
          ~arity:1
          [%expr
            fun input ->
              { input
              ; fieldsStatuses = initialFieldsStatuses input
              ; collectionsStatuses = initialCollectionsStatuses
              ; formStatus = Editing
              ; submissionStatus = NeverSubmitted
              }]]
    ;;]
;;
