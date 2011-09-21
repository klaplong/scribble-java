/*
 * Copyright 2009-11 www.scribble.org
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */
package org.scribble.protocol.model;

/**
 * This class represents a possible path of a directed choice, triggered
 * by a specified message signature.
 *
 */
public class OnMessage extends ModelObject {

    private MessageSignature _messageSignature=null;
    private Block _block=new Block();

    /**
     * This is the default constructor.
     * 
     */
    public OnMessage() {
        _block.setParent(this);
    }
    
    /**
     * This method returns the message signature.
     * 
     * @return The message signature
     */
    public MessageSignature getMessageSignature() {
        return (_messageSignature);
    }
    
    /**
     * This method sets the message signature.
     * 
     * @param signature The message signature
     */
    public void setMessageSignature(MessageSignature signature) {
        
        if (_messageSignature != null) {
            _messageSignature.setParent(null);
        }
        
        _messageSignature = signature;
        
        if (_messageSignature != null) {
            _messageSignature.setParent(this);
        }
    }
    
    /**
     * This method returns the activities.
     * 
     * @return The block of activities
     */
    public Block getBlock() {
        return (_block);
    }
    
    /**
     * This method sets the block.
     * 
     * @param block The block
     */
    public void setBlock(Block block) {
        if (_block != null) {
            _block.setParent(null);
        }
        
        _block = block;
        
        if (_block != null) {
            _block.setParent(this);
        }
    }

    /**
     * This method visits the model object using the supplied
     * visitor.
     * 
     * @param visitor The visitor
     */
    public void visit(Visitor visitor) {
        visitor.start(this);
        
        if (getBlock() != null) {
            getBlock().visit(visitor);
        }
        
        visitor.end(this);
    }    
}