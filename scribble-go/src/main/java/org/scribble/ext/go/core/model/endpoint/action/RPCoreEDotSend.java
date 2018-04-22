package org.scribble.ext.go.core.model.endpoint.action;

import org.scribble.ext.go.core.model.endpoint.RPCoreEModelFactory;
import org.scribble.ext.go.core.type.RPInterval;
import org.scribble.ext.go.core.type.RPIndexedRole;
import org.scribble.ext.go.type.index.RPIndexExpr;
import org.scribble.model.endpoint.actions.ESend;
import org.scribble.model.global.SModelFactory;
import org.scribble.model.global.actions.SSend;
import org.scribble.type.Payload;
import org.scribble.type.name.MessageId;
import org.scribble.type.name.Role;

public class RPCoreEDotSend extends ESend implements RPCoreEAction
{
	public final RPIndexExpr offset;

	// ParamRole range is original peer absolute range -- local id plus offset will be inside this range
	public RPCoreEDotSend(RPCoreEModelFactory ef, RPIndexedRole peer, RPIndexExpr offset, MessageId<?> mid, Payload payload)
	{
		super(ef, peer, mid, payload);
		this.offset = offset;
	}

	@Override
	public RPIndexedRole getPeer()
	{
		return (RPIndexedRole) this.peer;
	}

	@Override
	public RPCoreEDotReceive toDual(Role self)
	{
		throw new RuntimeException("[param-core] Shouldn't get in here: " + this);
	}

	@Override
	public SSend toGlobal(SModelFactory sf, Role self)
	{
		throw new RuntimeException("[param-core] Shouldn't get in here: " + this);
	}
	
	@Override
	public String toString()
	{
		RPIndexedRole peer = getPeer();
		RPInterval g = peer.intervals.iterator().next();
		return peer.getName() + "[" + this.offset + ":" + g.start + ".." + g.end + "]"
				+ getCommSymbol() + this.mid + this.payload;
	}

	@Override
	public String toStringWithMessageIdHack()
	{
		String m = this.mid.isMessageSigName() ? "^" + this.mid : this.mid.toString();  // HACK
		RPIndexedRole peer = getPeer();
		RPInterval g = peer.intervals.iterator().next();
		return peer.getName() + "[" + this.offset + ":" + g.start + ".." + g.end + "]"
				+ getCommSymbol() + m + this.payload;
	}
	
	@Override
	protected String getCommSymbol()
	{
		return "!=";
	}
	
	@Override
	public int hashCode()
	{
		int hash = 7211;
		hash = 31 * hash + super.hashCode();
		hash = 31 * hash + this.offset.hashCode();
		return hash;
	}

	@Override
	public boolean equals(Object o)
	{
		if (this == o)
		{
			return true;
		}
		if (!(o instanceof RPCoreEDotSend))
		{
			return false;
		}
		return super.equals(o)  // Does canEquals
				&& this.offset.equals(((RPCoreEDotSend) o).offset);
	}

	@Override
	public boolean canEqual(Object o)
	{
		return o instanceof RPCoreEDotSend;
	}
}
