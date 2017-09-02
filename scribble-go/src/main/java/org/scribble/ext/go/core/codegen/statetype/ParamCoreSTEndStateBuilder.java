package org.scribble.ext.go.core.codegen.statetype;

import org.scribble.codegen.statetype.STEndStateBuilder;
import org.scribble.codegen.statetype.STStateChanApiBuilder;
import org.scribble.model.endpoint.EState;

public class ParamCoreSTEndStateBuilder extends STEndStateBuilder
{
	public ParamCoreSTEndStateBuilder()
	{

	}
	
	@Override
	public String build(STStateChanApiBuilder api, EState s)
	{
		return getPreamble(api, s);
	}

	@Override
	public String getPreamble(STStateChanApiBuilder api, EState s)
	{
		//return GSTStateChanAPIBuilder.getStateChanPremable(api, s);
		String tname = api.getStateChanName(s);
		String res =
				  ParamCoreSTStateChanApiBuilder.getPackageDecl(api) + "\n"
				+ "\n"
				+ "import \"" + ParamCoreSTApiGenConstants.GO_SCRIBBLERUNTIME_PACKAGE + "\"\n"
				+ "\n"
				+ "type " + tname + " struct{\n"
				+ ParamCoreSTApiGenConstants.GO_SCHAN_ENDPOINT + " *" + ParamCoreSTApiGenConstants.GO_ENDPOINT_TYPE + "\n"  // FIXME: factor out
				+ "}";
		return res;  // No LinearResource
	}
}