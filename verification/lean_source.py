"""Inventory named shared declarations and prepare a before/after signature audit."""
from pathlib import Path
import json,re,hashlib

ROOT=Path(__file__).resolve().parent

def code_only(s):
    out=[];i=depth=0;string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
            elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif string:
            if s[i]=='\\' and i+1<len(s):out.extend('  ');i+=2
            else:string=s[i]!='"';out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
        elif s.startswith('--',i):
            end=s.find('\n',i)
            if end<0:break
            out.extend(' '*(end-i));i=end
        elif s[i]=='"':string=True;out.append(' ');i+=1
        else:out.append(s[i]);i+=1
    return ''.join(out)

def declarations(source):
    frames=[];out=[]
    for line in code_only(source).splitlines():
        command=re.sub(r'^(?:@\[[^\n]*?\]\s*)+','',line.strip())
        opened=re.fullmatch(r'namespace\s+([\w.]+)',command)
        section=re.fullmatch(r'(?:(?:noncomputable|public)\s+)*section(?:\s+([\w.]+))?',command)
        end=re.fullmatch(r'end(?:\s+([\w.]+))?',command)
        if opened:frames.append(('namespace',opened[1]));continue
        if section:frames.append(('section',section[1]));continue
        if end:
            if not frames:raise ValueError('Unmatched end: '+command)
            kind,name=frames.pop()
            if end[1] and end[1]!=name:raise ValueError('Mismatched end: '+command+' vs '+str(name))
            continue
        if re.match(r'(?:(?:noncomputable|public)\s+)*private\b',command):continue
        decl=re.match(r'(?:(?:noncomputable|public|protected)\s+)*(def|abbrev|theorem|lemma|structure|inductive|class|instance)\s+([\w.\']+)',command)
        if decl:
            prefix='.'.join(n for k,n in frames if k=='namespace')
            out.append({'kind':decl[1],'name':prefix+'.'+decl[2] if prefix else decl[2]})
    if any(k=='namespace' or n for k,n in frames):raise ValueError('Unclosed named scope: '+str(frames))
    return out

