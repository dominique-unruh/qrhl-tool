theory Universe_Instances
  imports Complex_Main Universe CryptHOL.Misc_CryptHOL
begin

no_notation HLD_nxt (infixr "\<cdot>" 65)

derive universe real
derive universe complex
derive universe nlist
derive universe blinfun
derive universe bcontfun
derive universe vec

end
