package org.scribble.del.global;

import org.scribble.ast.ScribNode;
import org.scribble.ast.global.GWrap;
import org.scribble.ast.local.LNode;
import org.scribble.del.ConnectionActionDel;
import org.scribble.main.ScribbleException;
import org.scribble.sesstype.Message;
import org.scribble.sesstype.name.Role;
import org.scribble.visit.GlobalModelBuilder;
import org.scribble.visit.NameDisambiguator;
import org.scribble.visit.Projector;
import org.scribble.visit.WFChoiceChecker;
import org.scribble.visit.env.WFChoiceEnv;

public class GWrapDel extends ConnectionActionDel implements GSimpleInteractionNodeDel
{
	public GWrapDel()
	{
		
	}

	@Override
	public ScribNode leaveDisambiguation(ScribNode parent, ScribNode child, NameDisambiguator disamb, ScribNode visited) throws ScribbleException
	{
		GWrap gw = (GWrap) visited;
		Role src = gw.src.toName();
		Role dest = gw.dest.toName();
		return gw;
	}

	@Override
	public GWrap leaveInlinedWFChoiceCheck(ScribNode parent, ScribNode child, WFChoiceChecker checker, ScribNode visited) throws ScribbleException
	{
		GWrap gw = (GWrap) visited;
		
		Role src = gw.src.toName();
		if (!checker.peekEnv().isEnabled(src))
		{
			throw new ScribbleException("Role not enabled: " + src);
		}
		Message msg = gw.msg.toMessage();  //  Unit message 
		Role dest = gw.dest.toName();
		if (src.equals(dest))
		{
			throw new ScribbleException("(TODO) Self connections not supported: " + gw);
		}
		WFChoiceEnv env = checker.popEnv();
		if (!env.isConnected(src, dest))
		{
			throw new ScribbleException("Roles not connected: " + src + ", " + dest);
		}

		//env = env.addMessage(src, dest, msg);
		/*env = env
				.connect(src, dest)
				.addMessage(src, dest, new MessageSig(Op.EMPTY_OPERATOR, Payload.EMPTY_PAYLOAD));*/
		checker.pushEnv(env);
		return gw;
	}

	@Override
	public ScribNode leaveProjection(ScribNode parent, ScribNode child, Projector proj, ScribNode visited) throws ScribbleException //throws ScribbleException
	{
		GWrap gw = (GWrap) visited;
		Role self = proj.peekSelf();
		LNode projection = gw.project(self);
		proj.pushEnv(proj.popEnv().setProjection(projection));
		return (GWrap) GSimpleInteractionNodeDel.super.leaveProjection(parent, child, proj, gw);
	}
	
	@Override
	public GWrap leaveModelBuilding(ScribNode parent, ScribNode child, GlobalModelBuilder builder, ScribNode visited) throws ScribbleException
	{
		//return (GConnect) super.leaveModelBuilding(parent, child, builder, ls);
		throw new RuntimeException("Shouldn't get in here: " + visited);
	}
}
