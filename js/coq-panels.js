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