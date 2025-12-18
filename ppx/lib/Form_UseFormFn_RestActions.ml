open Ppxlib
open Ast_helper

let ast ~loc ~async ~metadata =
  [ (if async
     then
       Exp.case
         [%pat? Submit]
         [%expr
           match state.formStatus with
           | Submitting _ -> NoUpdate
           | Editing | Submitted | SubmissionFailed _ ->
             let apply_validate
               : [%t
                   match metadata with
                   | None ->
                     Uncurried.ty
                       ~loc
                       ~arity:3
                       [%type:
                         input
                         -> validators:validators
                         -> fieldsStatuses:fieldsStatuses
                         -> ( output
                              , fieldsStatuses
                              , collectionsStatuses )
                              Async.formValidationResult]
                   | Some () ->
                     Uncurried.ty
                       ~loc
                       ~arity:4
                       [%type:
                         input
                         -> validators:validators
                         -> fieldsStatuses:fieldsStatuses
                         -> metadata:metadata
                         -> ( output
                              , fieldsStatuses
                              , collectionsStatuses )
                              Async.formValidationResult]]
               =
               [%e
                 match metadata with
                 | None ->
                   [%expr
                     [%e
                       Uncurried.fn
                         ~loc
                         ~arity:3
                         [%expr
                           fun input ~validators ~fieldsStatuses ->
                             validateForm input ~validators ~fieldsStatuses]]]
                 | Some () ->
                   [%expr
                     [%e
                       Uncurried.fn
                         ~loc
                         ~arity:4
                         [%expr
                           fun input ~validators ~fieldsStatuses ~metadata ->
                             validateForm input ~validators ~fieldsStatuses ~metadata]]]]
             in
             (match
                [%e
                  match metadata with
                  | None ->
                    [%expr
                      apply_validate
                        state.input
                        ~validators
                        ~fieldsStatuses:state.fieldsStatuses]
                  | Some () ->
                    [%expr
                      apply_validate
                        state.input
                        ~validators
                        ~fieldsStatuses:state.fieldsStatuses
                        ~metadata]]
              with
              | Validating { fieldsStatuses; collectionsStatuses } ->
                Update { state with fieldsStatuses; collectionsStatuses }
              | Valid { output; fieldsStatuses; collectionsStatuses } ->
                UpdateWithSideEffects
                  ( { state with
                      fieldsStatuses
                    ; collectionsStatuses
                    ; formStatus =
                        Submitting
                          (match state.formStatus with
                           | SubmissionFailed error -> Some error
                           | Editing | Submitted | Submitting _ -> None)
                    ; submissionStatus = AttemptedToSubmit
                    }
                  , [%e
                      Uncurried.fn
                        ~loc
                        ~arity:1
                        [%expr
                          fun { state = _; dispatch } ->
                            onSubmit
                              output
                              { notifyOnSuccess =
                                  [%e
                                    Uncurried.fn
                                      ~loc
                                      ~arity:1
                                      [%expr
                                        fun input -> dispatch (SetSubmittedStatus input)]]
                              ; notifyOnFailure =
                                  [%e
                                    Uncurried.fn
                                      ~loc
                                      ~arity:1
                                      [%expr
                                        fun error ->
                                          dispatch (SetSubmissionFailedStatus error)]]
                              ; reset =
                                  [%e
                                    Uncurried.fn
                                      ~loc
                                      ~arity:1
                                      [%expr fun () -> dispatch Reset]]
                              ; dismissSubmissionResult =
                                  [%e
                                    Uncurried.fn
                                      ~loc
                                      ~arity:1
                                      [%expr fun () -> dispatch DismissSubmissionResult]]
                              }]] )
              | Invalid { fieldsStatuses; collectionsStatuses } ->
                Update
                  { state with
                    fieldsStatuses
                  ; collectionsStatuses
                  ; formStatus = Editing
                  ; submissionStatus = AttemptedToSubmit
                  })]
     else
       Exp.case
         [%pat? Submit]
         [%expr
           match state.formStatus with
           | Submitting _ -> NoUpdate
           | Editing | Submitted | SubmissionFailed _ ->
             let apply_validate
               : [%t
                   match metadata with
                   | None ->
                     Uncurried.ty
                       ~loc
                       ~arity:3
                       [%type:
                         input
                         -> validators:validators
                         -> fieldsStatuses:fieldsStatuses
                         -> ( output
                              , fieldsStatuses
                              , collectionsStatuses )
                              formValidationResult]
                   | Some () ->
                     Uncurried.ty
                       ~loc
                       ~arity:4
                       [%type:
                         input
                         -> validators:validators
                         -> fieldsStatuses:fieldsStatuses
                         -> metadata:metadata
                         -> ( output
                              , fieldsStatuses
                              , collectionsStatuses )
                              formValidationResult]]
               =
               [%e
                 match metadata with
                 | None ->
                   [%expr
                     [%e
                       Uncurried.fn
                         ~loc
                         ~arity:3
                         [%expr
                           fun input ~validators ~fieldsStatuses ->
                             validateForm input ~validators ~fieldsStatuses]]]
                 | Some () ->
                   [%expr
                     [%e
                       Uncurried.fn
                         ~loc
                         ~arity:4
                         [%expr
                           fun input ~validators ~fieldsStatuses ~metadata ->
                             validateForm input ~validators ~fieldsStatuses ~metadata]]]]
             in
             (match
                [%e
                  match metadata with
                  | None ->
                    [%expr
                      apply_validate
                        state.input
                        ~validators
                        ~fieldsStatuses:state.fieldsStatuses]
                  | Some () ->
                    [%expr
                      apply_validate
                        state.input
                        ~validators
                        ~fieldsStatuses:state.fieldsStatuses
                        ~metadata]]
              with
              | Valid { output; fieldsStatuses; collectionsStatuses } ->
                UpdateWithSideEffects
                  ( { state with
                      fieldsStatuses
                    ; collectionsStatuses
                    ; formStatus =
                        Submitting
                          (match state.formStatus with
                           | SubmissionFailed error -> Some error
                           | Editing | Submitted | Submitting _ -> None)
                    ; submissionStatus = AttemptedToSubmit
                    }
                  , [%e
                      Uncurried.fn
                        ~loc
                        ~arity:1
                        [%expr
                          fun { state = _; dispatch } ->
                            onSubmit
                              output
                              { notifyOnSuccess =
                                  [%e
                                    Uncurried.fn
                                      ~loc
                                      ~arity:1
                                      [%expr
                                        fun input -> dispatch (SetSubmittedStatus input)]]
                              ; notifyOnFailure =
                                  [%e
                                    Uncurried.fn
                                      ~loc
                                      ~arity:1
                                      [%expr
                                        fun error ->
                                          dispatch (SetSubmissionFailedStatus error)]]
                              ; reset =
                                  [%e
                                    Uncurried.fn
                                      ~loc
                                      ~arity:1
                                      [%expr fun () -> dispatch Reset]]
                              ; dismissSubmissionResult =
                                  [%e
                                    Uncurried.fn
                                      ~loc
                                      ~arity:1
                                      [%expr fun () -> dispatch DismissSubmissionResult]]
                              }]] )
              | Invalid { fieldsStatuses; collectionsStatuses } ->
                Update
                  { state with
                    fieldsStatuses
                  ; collectionsStatuses
                  ; formStatus = Editing
                  ; submissionStatus = AttemptedToSubmit
                  })])
  ; Exp.case
      [%pat? SetSubmittedStatus input]
      [%expr
        match input with
        | Some input ->
          Update
            { state with
              input
            ; formStatus = Submitted
            ; fieldsStatuses = initialFieldsStatuses input
            }
        | None ->
          Update
            { state with
              formStatus = Submitted
            ; fieldsStatuses = initialFieldsStatuses state.input
            }]
  ; Exp.case
      [%pat? SetSubmissionFailedStatus error]
      [%expr Update { state with formStatus = SubmissionFailed error }]
  ; Exp.case
      [%pat? MapSubmissionError map]
      [%expr
        match state.formStatus with
        | Submitting (Some error) ->
          Update { state with formStatus = Submitting (Some (map error)) }
        | SubmissionFailed error ->
          Update { state with formStatus = SubmissionFailed (map error) }
        | Editing | Submitting None | Submitted -> NoUpdate]
  ; Exp.case
      [%pat? DismissSubmissionError]
      [%expr
        match state.formStatus with
        | Editing | Submitting _ | Submitted -> NoUpdate
        | SubmissionFailed _ -> Update { state with formStatus = Editing }]
  ; Exp.case
      [%pat? DismissSubmissionResult]
      [%expr
        match state.formStatus with
        | Editing | Submitting _ -> NoUpdate
        | Submitted | SubmissionFailed _ -> Update { state with formStatus = Editing }]
  ; Exp.case [%pat? Reset] [%expr Update (initialState initialInput)]
  ]
;;
