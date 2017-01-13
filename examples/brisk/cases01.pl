%%
%% From ../Data03.hs
%%
%% main := do me <- $getSelfPid
%%            _ <- $spawn((do me' <- $getSelfPid
%%                            _ <- $send[@PingMessage](me,(Ping(me')))
%%                            _ <- $expect[@PingMessage]
%%                            return Unit))
%%            msg <- $expect[@PingMessage]
%%            me <- $getSelfPid
%%            $send[@PingMessage](case msg of
%%                                  Ping ds_d5F0 ->
%%                                    ds_d5F0
%%                                  Pong ds_d5F1 ->
%%                                    ds_d5F1,(Pong(me)))
rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        T=par([ seq([ recv(A,type(PingMessage),msg),
                      assign(A,anf0,cases(A,msg,[ case(A,Ping(ds_d5F0),ds_d5F0),
                                                  case(A,Pong(ds_d5F1),ds_d5F1)])),
                      assign(A,anf1,Pong(A)),
                      send(A,PingMessage,e_var(anf0),anf1)]),
                seq([ assign(B,anf0,Ping(B)),
                      send(B,PingMessage,e_pid(A),anf0),
                      recv(B,type(PingMessage),_)])])
        Name='cases'.