var PackagesManager;

(function(){
    "use strict";
    PackagesManager = function(definitions_url, panel) {
        this.panel = panel;
        var req = new XMLHttpRequest();
        req.open('GET', definitions_url);
        req.send(null);

        req.addEventListener('readystatechange',
                             () => {
                                 if(req.readyState === 4 &&
                                    (req.status === 200 || req.status === 304))
                                    this.displayDefinitions(req);
                             });
    };

    PackagesManager.prototype.displayDefinitions = function(req) {
        var self = this;
        var rows = d3.select(this.panel).selectAll('div')
            .data(JSON.parse(req.responseText))
            .enter()
            .append('div');
        rows.each(function() {
            var row = d3.select(this);
            row.append('img')
                .attr('src', 'images/dl.png')
                .on('click', function(){self.downloadPackage();});
            row.append('span')
                .text(function(d){return d.pkg_id[0] + ' – ' + d.pkg_id[1];});

        });
    };

    PackagesManager.prototype.downloadPackage = function() {
        var package_info = d3.select(d3.event.target.parentNode).datum();
        console.log(package_info);
    };
}());