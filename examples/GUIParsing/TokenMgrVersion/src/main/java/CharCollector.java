/*
 * Copyright (c) 2020-2025, Sreeni Viswanadha <sreeni@viswanadha.net>.
 * Copyright (c) 2024-2025, Marc Mazas <mazas.marc@gmail.com>.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *     * Redistributions of source code must retain the above copyright notice,
 *       this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the names of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived from
 *       this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
 * THE POSSIBILITY OF SUCH DAMAGE.
 */
/**
 * A CharStream implementation for an event driven stream that produces / consumes one character at
 * a time.<br>
 * Adapted from the SimpleCharStream, removing constructors and reinitialize methods, removing
 * internal lines & columns updates (which is different from lines & columns tracking), filling the
 * buffer directly.
 */
public class CharCollector implements CharStream {

  int bufsize;
  int available;
  int tokenBegin;
  public int bufpos = -1;

  protected char[] buffer;
  protected int maxNextCharInd = 0;
  protected int inBuf = 0;

  protected boolean trackLineColumn = true;
  protected int tabSize = 1;
  private char nextChar;

  /** Puts a character into the buffer. Called by the GUI. */
  public final synchronized void put(char c) {
    buffer[maxNextCharInd++] = c;
    notify();
  }

  public void Clear() {
    bufpos = -1;
    maxNextCharInd = 0;
    inBuf = 0;
  }

  public char BeginToken() throws java.io.IOException {
    tokenBegin = -1;
    char c = readChar();
    tokenBegin = bufpos;

    return c;
  }

  // same as in SimpleCharStream but shorter (and with chars forced in the ASCII range)
  public final synchronized char readChar() throws java.io.IOException {
    if (inBuf > 0) {
      --inBuf;
      return (char) ((char) 0xff & buffer[(bufpos == bufsize - 1) ? (bufpos = 0) : ++bufpos]);
    }

    if (++bufpos >= maxNextCharInd) {
      FillBuff();
    }
    return buffer[bufpos];
  }

  private final void FillBuff() {
    if (maxNextCharInd == available) {
      if (available == bufsize) {
        if (tokenBegin > 2048) {
          bufpos = maxNextCharInd = 0;
          available = tokenBegin;
        } else if (tokenBegin < 0) {
          bufpos = maxNextCharInd = 0;
        } else {
          ExpandBuff(false);
        }
      } else if (available > tokenBegin) {
        available = bufsize;
      } else if ((tokenBegin - available) < 2048) {
        ExpandBuff(true);
      } else {
        available = tokenBegin;
      }
    }
    try {
      wait();
    } catch (InterruptedException willNotHappen) {
      throw new Error();
    }
  }

  private final void ExpandBuff(boolean wrapAround) {
    char[] newbuffer = new char[bufsize + 2048];

    try {
      if (wrapAround) {
        System.arraycopy(buffer, tokenBegin, newbuffer, 0, bufsize - tokenBegin);
        System.arraycopy(buffer, 0, newbuffer, bufsize - tokenBegin, bufpos);
        buffer = newbuffer;
        maxNextCharInd = (bufpos += (bufsize - tokenBegin));
      } else {
        System.arraycopy(buffer, tokenBegin, newbuffer, 0, bufsize - tokenBegin);
        buffer = newbuffer;
        maxNextCharInd = (bufpos -= tokenBegin);
      }
    } catch (Throwable t) {
      System.out.println("Error : " + t.getClass().getName());
      throw new Error();
    }

    bufsize += 2048;
    available = bufsize;
    tokenBegin = 0;
  }

  public final void backup(int amount) {
    inBuf += amount;
    if ((bufpos -= amount) < 0) {
      bufpos += bufsize;
    }
  }

  public void Done() {
    buffer = null;
  }

  public final String GetImage() {
    if (bufpos >= tokenBegin) {
      return new String(buffer, tokenBegin, bufpos - tokenBegin + 1);
    } else
      return new String(buffer, tokenBegin, bufsize - tokenBegin)
          + new String(buffer, 0, bufpos + 1);
  }

  public final char[] GetSuffix(int len) {
    char[] ret = new char[len];
    if (bufpos + 1 >= len) {
      System.arraycopy(buffer, bufpos - len + 1, ret, 0, len);
    } else {
      System.arraycopy(buffer, bufsize - (len - bufpos - 1), ret, 0, len - bufpos - 1);
      System.arraycopy(buffer, 0, ret, len - bufpos, bufpos + 1);
    }
    return ret;
  }

  public CharCollector() {
    available = bufsize = 4096;
    buffer = new char[4096];
  }

  @Deprecated
  public final int getLine() {
    return 0;
  }

  @Deprecated
  public final int getColumn() {
    return 0;
  }

  public final int getBeginLine() {
    return 0;
  }

  public final int getBeginColumn() {
    return 0;
  }

  public final int getEndLine() {
    return 0;
  }

  public final int getEndColumn() {
    return 0;
  }

  public boolean getTrackLineColumn() {
    return trackLineColumn;
  }

  public void setTrackLineColumn(boolean tlc) {
    trackLineColumn = tlc;
  }

  public int getTabSize() {
    return tabSize;
  }

  public void setTabSize(int i) {
    tabSize = i;
  }

  /**
   * Returns next character.
   *
   * @return next character in the input
   */
  public char getNextChar() {
    return nextChar;
  }

  /**
   * Checks next character.
   *
   * @return whether next character is available
   */
  public boolean hasNextChar() {
    try {
      nextChar = readChar();
      return true;
    } catch (java.io.IOException ex) {
      return false;
    }
  }

  /**
   * Checks next character and marks new token.
   *
   * @return whether next character is available
   */
  public boolean hasNextToken() {
    try {
      nextChar = BeginToken();
      return true;
    } catch (java.io.IOException ex) {
      return false;
    }
  }
}
