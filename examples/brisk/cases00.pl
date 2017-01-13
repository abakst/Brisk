%%
%% From ../Data01.hs
%%
%% main := do me <- $getSelfPid
%%            _ <- $spawn((do me' <- $getSelfPid
%%                            _ <- $send[@PingMessage](me,(Ping(me')))
%%                            _ <- $expect[@PingMessage]
%%                            return Unit))
%%            msg <- $expect[@PingMessage]
%%            case msg of
%%              Ping whom ->
%%                do me <- $getSelfPid
%%                   $send[@PingMessage](whom,(Pong(me)))
%%              _ -> return Unit
rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        T=par([ seq([ recv(A,type(PingMessage),msg),
                      cases(A,msg,[ case(A,Ping(whom),seq([ assign(A,anf0,Pong(A)),
                                                            send(A,PingMessage,e_var(whom),anf0)])),
                                    case(A,default(),skip)])]),
                seq([ assign(B,anf0,Ping(B)),
                      send(B,PingMessage,e_pid(A),anf0),
                      recv(B,type(PingMessage),_)])]),
        Name='cases'.