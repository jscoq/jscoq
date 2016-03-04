"use strict";

class Panel {

    constructor(panel_elt) {
        this.panel_elt = panel_elt
    }
}


class ProofPanel extends Panel {

    display(text) {
        this.panel_elt.innerText = text;
    }
}

class QueryPanel extends Panel {

    log(msg, level) {
        d3.select(this.panel_elt)
            .append('div')
            .attr('class', level)
            .html(msg)
            .node()
            .scrollIntoView();
    }
}

class NavbarPanel extends Panel {

    constructor(panel_elt, coq_manager) {
        super(panel_elt);
        this.coq_manager = coq_manager;
        window.addEventListener('load', evt => this._initListeners());
    }

    _initListeners() {
        var coq_exec_btns = document.getElementsByClassName('coq-exec-btns')[0];
        coq_exec_btns.addEventListener('click', evt => this.toolbarClickHandler(evt));
    }

    toolbarClickHandler(evt) {
        var target = evt.target;
        target.blur();

        switch (target.name) {
            case 'to-cursor' :
                this.coq_manager.goCursor();
                break;

            case 'up' :
                this.coq_manager.goPrev();
                break;

            case 'down' :
                this.coq_manager.goNext(true);
                break;
        }
    }

    raiseButton(btn_name) {
        var btn = d3.select(this.panel_elt)
            .select(`.coq-exec-btns button[name=${btn_name}]`)
            .node();
        if (btn)
            btn.dispatchEvent(new MouseEvent('click',
                                             {'view'       : window,
                                              'bubbles'    : true,
                                              'cancelable' : true}));
    }
}